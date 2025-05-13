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
 

   // Internal definitions
    localparam TX_IDLE   = 3'b000,
               TX_START  = 3'b001,
               TX_DATA   = 3'b010,
               TX_PARITY = 3'b011,
               TX_STOP   = 3'b100;

    localparam RX_IDLE   = 3'b000,
               RX_START  = 3'b001,
               RX_DATA   = 3'b010,
               RX_PARITY = 3'b011,
               RX_STOP   = 3'b100,
               RX_SAVE   = 3'b101;

    localparam ADDR_CONFIG = 4'h0,
               ADDR_TX     = 4'h2,
               ADDR_RX     = 4'h3,
               ADDR_STATUS = 4'h4;

    parameter BAUD_DIV = 16;
    localparam FIFO_DEPTH = 16;

    reg [2:0] tx_state, rx_state;
    reg [7:0] tx_shift_reg, rx_shift_reg;
    reg [3:0] tx_bit_cnt, rx_bit_cnt;
    reg [15:0] baud_cnt, rx_baud_cnt;
    reg [3:0] rx_sample_cnt;

    reg [7:0] reg_config, reg_status, reg_rx;
    reg [7:0] fifo [0:FIFO_DEPTH-1];
    reg [3:0] wr_ptr, rd_ptr;
    reg [4:0] count;

    wire full  = (count == FIFO_DEPTH);
    wire empty = (count == 0);

    wire [3:0] data_bits = (reg_config[1:0]==2'b00)?5:
                           (reg_config[1:0]==2'b01)?6:
                           (reg_config[1:0]==2'b10)?7:8;

    // PREADY signal
    always @(posedge pclk or negedge preset_n)
        if (!preset_n) pready <= 1'b0;
        else           pready <= 1'b1;

    // APB interface
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            reg_config <= 0; reg_status <= 0; reg_rx <= 0;
            wr_ptr <= 0; rd_ptr <= 0; count <= 0;
            prdata <= 0;
        end else if (psel && penable) begin
            if (pwrite) begin
                case(paddr)
                    ADDR_CONFIG: reg_config <= pwdata;
                    ADDR_TX: if (!full) begin
                        fifo[wr_ptr] <= pwdata;
                        wr_ptr <= wr_ptr + 1;
                        count  <= count + 1;
                    end else reg_status[1] <= 1'b1;
                    ADDR_RX: reg_rx <= pwdata;
                endcase
            end else begin
                case(paddr)
                    ADDR_CONFIG: prdata <= reg_config;
                    ADDR_TX:     prdata <= {7'd0, full};
                    ADDR_RX:     begin prdata <= reg_rx; reg_status[2] <= 1'b0; end
                    ADDR_STATUS: prdata <= reg_status;
                    default:     prdata <= 0;
                endcase
            end
        end
    end

    // TX logic
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            tx_state <= TX_IDLE; tx_bit_cnt <= 0; baud_cnt <= 0;
            uart_tx <= 1'b1;
        end else begin
            if (baud_cnt < BAUD_DIV-1)
                baud_cnt <= baud_cnt + 1;
            else begin
                baud_cnt <= 0;
                case(tx_state)
                    TX_IDLE: begin
                        uart_tx <= 1'b1;
                        if (!empty && rx_state==RX_IDLE) begin
                            tx_shift_reg <= fifo[rd_ptr];
                            rd_ptr <= rd_ptr + 1; count <= count - 1;
                            tx_state <= TX_START; uart_tx <= 1'b0; tx_bit_cnt <= 0;
                        end
                    end
                    TX_START: tx_state <= TX_DATA;
                    TX_DATA: begin
                        uart_tx <= tx_shift_reg[0];
                        tx_shift_reg <= {1'b0, tx_shift_reg[7:1]};
                        tx_bit_cnt <= tx_bit_cnt + 1;
                        if (tx_bit_cnt == data_bits - 1)
                            tx_state <= reg_config[2] ? TX_PARITY : TX_STOP;
                    end
                    TX_PARITY: tx_state <= TX_STOP;
                    TX_STOP:   tx_state <= TX_IDLE;
                endcase
            end
        end
    end

    // RX logic
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            rx_state <= RX_IDLE; rx_bit_cnt <= 0; rx_baud_cnt <= 0; rx_sample_cnt <= 0;
        end else begin
            case(rx_state)
                RX_IDLE: begin
                    if (uart_rx == 0 && tx_state == TX_IDLE && empty) begin
                        rx_state <= RX_START; rx_sample_cnt <= 0;
                    end
                end
                RX_START: begin
                    rx_sample_cnt <= rx_sample_cnt + 1;
                    if (rx_sample_cnt == (BAUD_DIV/2)) begin
                        if (uart_rx == 0) begin
                            rx_baud_cnt <= 0; rx_bit_cnt <= 0; rx_state <= RX_DATA;
                        end else rx_state <= RX_IDLE;
                    end
                end
                RX_DATA: begin
                    if (rx_baud_cnt < BAUD_DIV-1) rx_baud_cnt <= rx_baud_cnt + 1;
                    else begin
                        rx_baud_cnt <= 0;
                        rx_shift_reg <= {rx_shift_reg[6:0], uart_rx};
                        rx_bit_cnt <= rx_bit_cnt + 1;
                        if (rx_bit_cnt == data_bits - 1)
                            rx_state <= reg_config[2] ? RX_PARITY : RX_STOP;
                    end
                end
                RX_PARITY: rx_state <= RX_STOP;
                RX_STOP: begin
                    if (rx_baud_cnt < BAUD_DIV-1) rx_baud_cnt <= rx_baud_cnt + 1;
                    else begin
                        rx_baud_cnt <= 0;
                        if (uart_rx == 1) rx_state <= RX_SAVE;
                        else rx_state <= RX_IDLE;
                    end
                end
                RX_SAVE: begin
                    if (reg_status[2]) reg_status[3] <= 1'b1;
                    else begin
                        reg_rx <= rx_shift_reg;
                        reg_status[2] <= 1'b1;
                    end
                    rx_state <= RX_IDLE;
                end
            endcase
        end
    end

    // Status update
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) reg_status <= 8'b00000001;
        else begin
            reg_status[0] <= empty;
            reg_status[1] <= full;
        end
    end

    // Interrupts
    always @(posedge pclk or negedge preset_n) begin
        if (!preset_n) int_o <= 3'b000;
        else begin
            int_o[0] <= reg_status[1];
            int_o[1] <= reg_status[3];
            int_o[2] <= reg_status[4];
        end
    end

endmodule

