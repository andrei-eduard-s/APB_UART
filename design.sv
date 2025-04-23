module uart_apb_dut(pclk, preset_n, paddr, psel, penable, pwrite, pwdata, prdata, pready, uart_rx, uart_tx, int_o);

  // Interfata apb
    input              pclk;       // semnal de ceas
    input              preset_n;   // semnal de reset, activ low
    input       [3:0]  paddr;      // adresa apb
    input              psel;       // selectia slave-ului
    input              penable;    // activare tranzactie
    input              pwrite;     // 1: scriere, 0: citire
    input       [7:0]  pwdata;     // date de scriere
    output reg  [7:0]  prdata;     // date citite
    output reg         pready;     // semnal gata (simplificat: mereu 1, dupa reset)
    
    // Interfata UART
    input              uart_rx;    // linia de receptie seriala (intrare)
    output reg         uart_tx;    // linia de transmisie seriala (iesire)
    
    // Interfata de intreruperi (3 iesiri pentru diferite conditii)
    output reg  [2:0]  int_o;       // [0]: TX FIFO plin, [1]: RX overrun, [2]: TX error
  // Logica pentru semnalul pready:
    // In timpul reset-ului, pready = 0, iar dupa reset, pready = 1.
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n)
            pready <= 1'b0;
        else
            pready <= 1'b1;
    end

    // Predeclarari pentru state machine-urile TX si RX
    // Starile pentru TX:
    localparam TX_IDLE   = 3'b000;
    localparam TX_START  = 3'b001;
    localparam TX_DATA   = 3'b010;
    localparam TX_PARITY = 3'b011;
    localparam TX_STOP   = 3'b100;
    // Starile pentru RX:
    localparam RX_IDLE   = 3'b000;
    localparam RX_START  = 3'b001;
    localparam RX_DATA   = 3'b010;
    localparam RX_PARITY = 3'b011;
    localparam RX_STOP   = 3'b100;

    // Declaratii pentru state machine-urile TX si RX
    reg [2:0] tx_state;
    reg [2:0] rx_state;
    reg [7:0] tx_shift_reg;
    reg [7:0] rx_shift_reg;
    reg [3:0] tx_bit_cnt;
    reg [3:0] rx_bit_cnt;
    reg [15:0] baud_counter;
    reg [15:0] rx_baud_counter;
    parameter BAUD_DIV = 16;  // Factor de divizare pentru rata de baud (ajustabil)

    // Restul declaratiilor interne
    // Definitia adreselor registrelor interne
    localparam ADDR_CONFIG = 4'h0; // Registru de configurare UART
    // Eliminat: localparam ADDR_CTRL   = 4'h1; // Registru de control (ex. enable UART)
    localparam ADDR_TX     = 4'h2; // Registru pentru scriere in FIFO-ul TX
    localparam ADDR_RX     = 4'h3; // Registru pentru citirea datelor RX
    localparam ADDR_STATUS = 4'h4; // Registru de stare (flag-uri)

    // Registre interne
    // reg_config: [1:0] - numarul de biti de date:
    //    00: 5 biti, 01: 6 biti, 10: 7 biti, 11: 8 biti;
    // bit [2]: activare paritate, [3]: tip paritate (0: paritate para, 1: impara);
    // bit [4]: numar stop bits (0: 1 stop, 1: 2 stop).
    reg [7:0] reg_config;
    // Eliminat: reg_ctrl - registrul de control a fost eliminat
    // reg_status:
    // [0]: TX FIFO gol, [1]: TX FIFO plin, [2]: date RX valide, [3]: eroare de suprascriere RX, [4]: eroare TX
    reg [7:0] reg_status;
    // Registrul pentru datele receptionate
    reg [7:0] reg_rx;

    // Implementarea unui FIFO simplu pentru TX
    localparam FIFO_DEPTH = 16;
    reg [7:0] fifo_tx [0:FIFO_DEPTH-1];
    reg [3:0] fifo_wr_ptr;
    reg [3:0] fifo_rd_ptr;
    reg [4:0] fifo_count; // contor pentru elementele din FIFO

    wire fifo_full  = (fifo_count == FIFO_DEPTH);
    wire fifo_empty = (fifo_count == 0);

    // Determinarea numarului de biti de date pe baza reg_config[1:0]:
    // 00 -> 5, 01 -> 6, 10 -> 7, 11 -> 8
    wire [3:0] data_bits;
    assign data_bits = (reg_config[1:0] == 2'b00) ? 5 :
                       (reg_config[1:0] == 2'b01) ? 6 :
                       (reg_config[1:0] == 2'b10) ? 7 : 8;

    // Logica interfetei APB: scriere/citire in/din registre
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            reg_config   <= 8'd0;
            // Eliminat: reg_ctrl <= 8'd0;
            reg_status   <= 8'd0;
            reg_rx       <= 8'd0;
            fifo_wr_ptr  <= 0;
            fifo_rd_ptr  <= 0;
            fifo_count   <= 0;
            prdata       <= 8'd0;
        end else begin
            if (psel && penable) begin
                if (pwrite) begin
                    case (paddr)
                        ADDR_CONFIG: reg_config <= pwdata;
                        // Eliminat: ADDR_CTRL (registrul de control)
                        ADDR_TX: begin
                            if (!fifo_full) begin
                                fifo_tx[fifo_wr_ptr] <= pwdata;
                                fifo_wr_ptr <= fifo_wr_ptr + 1;
                                fifo_count  <= fifo_count + 1;
                            end else begin
                                // Daca FIFO-ul este plin, se seteaza flag-ul de eroare
                                reg_status[1] <= 1'b1;
                            end
                        end
                        default: ;
                    endcase
                end else begin // operatie de citire
                    case (paddr)
                        ADDR_CONFIG: prdata <= reg_config;
                        // Eliminat: ADDR_CTRL: prdata <= reg_ctrl;
                        // Citirea din registrul TX returneaza flag-ul de plinitate a FIFO-ului
                        ADDR_TX:     prdata <= {7'd0, fifo_full};
                        ADDR_RX: begin
                            prdata <= reg_rx;
                            // La citirea datelor RX, se sterge flag-ul "date valide"
                            reg_status[2] <= 1'b0;
                        end
                        ADDR_STATUS: prdata <= reg_status;
                        default:     prdata <= 8'd0;
                    endcase
                end
            end
        end
    end

    // =================================================================
    // State Machine pentru Transmisia UART (TX)
    // =================================================================
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            tx_state     <= TX_IDLE;
            tx_bit_cnt   <= 0;
            baud_counter <= 0;
            uart_tx      <= 1'b1; // linia TX este la nivel logic 1 in stare de repaus
        end else begin
            // Generatorul de baud rate
            if (baud_counter < BAUD_DIV - 1)
                baud_counter <= baud_counter + 1;
            else begin
                baud_counter <= 0;
                case (tx_state)
                    TX_IDLE: begin
                        uart_tx <= 1'b1;
                        // Daca FIFO-ul nu este gol si nu exista tranzactie pe RX (rx_state in idle)
                        if (!fifo_empty && (rx_state == RX_IDLE)) begin
                            tx_shift_reg <= fifo_tx[fifo_rd_ptr];
                            fifo_rd_ptr  <= fifo_rd_ptr + 1;
                            fifo_count   <= fifo_count - 1;
                            tx_state     <= TX_START;
                            uart_tx      <= 1'b0; // bit de start (0)
                        end
                    end
                    TX_START: begin
                        // Se trece la transmiterea datelor
                        tx_state   <= TX_DATA;
                        tx_bit_cnt <= 0;
                    end
                    TX_DATA: begin
                        uart_tx    <= tx_shift_reg[0];  // transmitere LSB
                        tx_shift_reg <= {1'b0, tx_shift_reg[7:1]}; // shiftare spre dreapta
                        tx_bit_cnt <= tx_bit_cnt + 1;
                        if (tx_bit_cnt == data_bits - 1) begin
                            if (reg_config[2]) // daca paritatea este activata
                                tx_state <= TX_PARITY;
                            else
                                tx_state <= TX_STOP;
                        end
                    end
                    TX_PARITY: begin
                        // Calculul paritatii poate fi implementat aici; pentru simplitate se transmite un bit de paritate "0"
                        uart_tx <= 1'b0; // bit de paritate (placeholder)
                        tx_state <= TX_STOP;
                    end
                    TX_STOP: begin
                        uart_tx <= 1'b1; // bit de stop (nivel logic 1)
                        tx_state <= TX_IDLE;
                    end
                    default: tx_state <= TX_IDLE;
                endcase
            end
        end
    end

    // =================================================================
    // State Machine pentru Receptia UART (RX)
    // =================================================================
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            rx_state         <= RX_IDLE;
            rx_bit_cnt       <= 0;
            rx_baud_counter  <= 0;
        end else begin
            if (rx_baud_counter < BAUD_DIV - 1)
                rx_baud_counter <= rx_baud_counter + 1;
            else begin
                rx_baud_counter <= 0;
                case (rx_state)
                    RX_IDLE: begin
                        // Se initiaza receptia doar daca nu exista tranzactie pe TX
                        if ((uart_rx == 1'b0) && (tx_state == TX_IDLE) && fifo_empty)
                            rx_state <= RX_START;
                    end
                    RX_START: begin
                        // Se esantioneaza bitul de start la mijlocul intervalului
                        if (uart_rx == 1'b0) begin
                            rx_state   <= RX_DATA;
                            rx_bit_cnt <= 0;
                        end else
                            rx_state <= RX_IDLE; // eroare de sincronizare
                    end
                    RX_DATA: begin
                        // Colectare biti de date (LSB intai)
                        rx_shift_reg <= {uart_rx, rx_shift_reg[7:1]};
                        rx_bit_cnt <= rx_bit_cnt + 1;
                        if (rx_bit_cnt == data_bits - 1) begin
                            if (reg_config[2])  // daca se foloseste paritate
                                rx_state <= RX_PARITY;
                            else
                                rx_state <= RX_STOP;
                        end
                    end
                    RX_PARITY: begin
                        // Pentru simplitate, se sare peste verificarea paritatii
                        rx_state <= RX_STOP;
                    end
                    RX_STOP: begin
                        // Verificare bit de stop (ar trebui sa fie '1')
                        if (uart_rx == 1'b1) begin
                            // Daca datele anterioare nu au fost citite, se seteaza eroarea de suprascriere (overrun)
                            if (reg_status[2] == 1'b1)
                                reg_status[3] <= 1'b1; // RX overrun
                            else begin
                                reg_rx <= rx_shift_reg;
                                reg_status[2] <= 1'b1; // semnalizeaza ca exista date RX valide
                            end
                        end
                        rx_state <= RX_IDLE;
                    end
                    default: rx_state <= RX_IDLE;
                endcase
            end
        end
    end

    // Actualizarea flag-urilor de stare pentru TX FIFO gol/plin
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            reg_status[0] <= 1'b1; // FIFO TX este gol la reset
            reg_status[1] <= 1'b0;
        end else begin
            reg_status[0] <= fifo_empty;
            reg_status[1] <= fifo_full;
            // Flag-ul pentru eroare TX (reg_status[4]) nu este implementat detaliat aici
            reg_status[4] <= 1'b0;
        end
    end

    // Generarea semnalelor de intrerupere:
    // int_o[0]: TX FIFO plin
    // int_o[1]: eroare RX (suprascriere)
    // int_o[2]: eroare TX (placeholder)
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n)
            int_o <= 3'b0;
        else begin
            int_o[0] <= fifo_full;
            int_o[1] <= reg_status[3];
            int_o[2] <= reg_status[4];
        end
    end

endmodule