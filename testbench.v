`timescale 1ns/1ps

module tb_uart_apb_dut;

    // Semnale APB
    reg         pclk;
    reg         preset_n;
    reg  [3:0]  paddr;
    reg         psel;
    reg         penable;
    reg         pwrite;
    reg  [7:0]  pwdata;
    wire [7:0]  prdata;
    wire        pready;
    
    // Semnale UART
    reg         uart_rx;
    wire        uart_tx;
    
    // Semnale de intreruperi
    wire [2:0]  int_o;
    
    // Instantierea DUT-ului
    uart_apb_dut dut (
        .pclk(pclk),
        .preset_n(preset_n),
        .paddr(paddr),
        .psel(psel),
        .penable(penable),
        .pwrite(pwrite),
        .pwdata(pwdata),
        .prdata(prdata),
        .pready(pready),
        .uart_rx(uart_rx),
        .uart_tx(uart_tx),
        .int_o(int_o)
    );
    
    // Generare semnal de ceas: perioada de 10 ns (100 MHz)
    initial begin
        pclk = 0;
        forever #5 pclk = ~pclk;
    end

    // Secventa de test
    initial begin
        // Initializari
        preset_n = 0;
        paddr    = 4'd0;
        psel     = 0;
        penable  = 0;
        pwrite   = 0;
        pwdata   = 8'd0;
        uart_rx  = 1;  // linia RX inactiva (nivel 1)
        #20;
        
        // Eliberare reset
        preset_n = 1;
        #20;
        
        // Scriere in registrul de configurare:
        // Setare: 8 biti de date (reg_config[1:0]=11), fara paritate (bit 2=0) si 1 stop bit (bit 4=0)
        apb_write(4'h0, 8'b00000011);
        
        // Scrierea unui caracter in FIFO-ul TX pentru a initia tranzactia de TX
        apb_write(4'h2, 8'h41);  // caracterul 'A'
        
        // Asteapta cateva cicluri pentru a permite inceputul tranzactiei TX
        #30;
        
        // Se incearca simularea unei tranzactii RX in paralel cu TX
        fork
            begin
                // Se simuleaza RX in timpul unei tranzactii TX active
                simulate_uart_rx(8'hAA);
            end
            begin
                // Asteapta timp pentru ca TX sa fie in curs
                #100;
            end
        join
        
        // Asteapta ca tranzactia TX sa se incheie
        #200;
        
        // Citire din registrul de stare pentru verificarea flag-urilor dupa TX
        apb_read(4'h4);
        
        // Simulare tranzactie RX dupa terminarea TX (acum ar trebui acceptata)
        simulate_uart_rx(8'h55);
        #200;
        
        // Citire din registrul RX pentru a obtine octetul receptionat
        apb_read(4'h3);
        
        #200;
        $stop;
    end

    // Task pentru operatia APB de scriere
    task apb_write(input [3:0] addr, input [7:0] data);
    begin
        @(posedge pclk);
        paddr  <= addr;
        pwdata <= data;
        psel   <= 1;
        pwrite <= 1;
        penable<= 0;
        @(posedge pclk);
        penable<= 1;
        @(posedge pclk);
        $display("Time %t: APB Write - Addr: %h, Data: %h", $time, addr, data);
        psel   <= 0;
        penable<= 0;
        pwrite <= 0;
    end
    endtask

    // Task pentru operatia APB de citire
    task apb_read(input [3:0] addr);
    begin
        @(posedge pclk);
        paddr  <= addr;
        psel   <= 1;
        pwrite <= 0;
        penable<= 0;
        @(posedge pclk);
        penable<= 1;
        @(posedge pclk);
        $display("Time %t: APB Read - Addr: %h, Data: %h", $time, addr, prdata);
        psel   <= 0;
        penable<= 0;
    end
    endtask

    // Parametru pentru perioada de baud: BAUD_DIV=16, perioada ceasului=10 ns => BAUD_PERIOD=160 ns
    parameter BAUD_PERIOD = 160;

    // Task pentru simularea receptiei UART a unui octet
    task simulate_uart_rx(input [7:0] rx_byte);
        integer i;
        begin
            $display("Time %t: Simulating UART RX - Byte: %h", $time, rx_byte);
            // Bitul de start (nivel 0)
            uart_rx = 0;
            #BAUD_PERIOD;
            // Transmiterea bitilor de date (LSB intai)
            for (i = 0; i < 8; i = i + 1) begin
                uart_rx = rx_byte[i];
                #BAUD_PERIOD;
            end
            // Bitul de stop (nivel 1)
            uart_rx = 1;
            #BAUD_PERIOD;
        end
    endtask

endmodule
