`include "uvm_macros.svh"
import uvm_pkg::*;

`define PERIOADA_CEASULUI 10


//`define DEBUG      //parametru folosit pentru a activa mesaje pe care noi le stabilim ca ar fi necesare doar la debug

//stabilirea semnificatiei unitatilor de timp din simulator
`timescale 1ns/1ns

//includerea fisierelor la care modulul de top trebuie sa aiba acces

`include "apb_interface_dut.sv"
`include "irq_interface_dut.sv"
`include "uart_interface_dut.sv"
`include "test_exemplu.sv"
`include "design.sv"

// Code your testbench here

module top();
   logic        clk;
   logic        preset_n;
   wire  [3:0]  paddr;
   wire         psel;
   wire         penable;
   wire         pwrite;   
   wire  [7:0]  pwdata;   
   wire  [7:0]  prdata;   
   wire         pready;   
   wire         uart_rx;  
   logic        uart_tx;  
   wire  [2:0]  int_o;    
   
  //sunt create instantele interfetelor (in acest proiect sunt 2 agenti, deci vor fi 2 interfete); se leaga semnalele interfetelor de semnalele din modulul de top
  apb_interface_dut intf_apb();
  assign intf_apb.pclk     = clk;
  assign intf_apb.preset_n = preset_n;
  assign psel              = intf_apb.psel;
  assign penable           = intf_apb.penable;
  assign paddr             = intf_apb.paddr;
  assign pwrite            = intf_apb.pwrite;
  assign pwdata            = intf_apb.pwdata;
  assign intf_apb.prdata   = prdata;
  assign intf_apb.pready   = pready;  
  
  irq_interface_dut intf_irq();
  assign intf_irq.clk   = clk;
  assign preset_n       = intf_irq.reset_n;
  assign intf_irq.int_o = int_o;

  uart_interface_dut intf_uart();
  assign intf_uart.clk_i   = clk;
  assign intf_uart.reset_n = preset_n;
  assign uart_tx           = intf_uart.uart_tx;
  assign intf_uart.uart_rx = uart_rx;


  initial begin
    //cele 2 linii de mai jos permit vizualizarea formelor de unda (pentru a vizualiza formele de unda trebuie bifata si optiunea "Open EPWave after run" din sectiunea "Tools & Simulators" aflata in stanga paginii)
    $dumpfile("dump.vcd");
    $dumpvars;
    //se genereaza ceasul
	  clk = 1;
	  forever begin 
      #(`PERIOADA_CEASULUI/2)  
      clk <= ~clk;
    end
	end

  initial begin
    // Initialize UART and APB reset to inactive (0 = asserted for active-low reset)
    preset_n <= 0;
    //initialise APB lines to idle
    intf_apb.paddr    <= 0;
    intf_apb.penable  <= 0;
    intf_apb.psel     <= 0;
    // Initialize UART lines to idle (HIGH)
    intf_uart.uart_tx <= 1;
    intf_uart.uart_rx <= 1;

    // Hold reset for a few clock cycles
    repeat (15) @(posedge clk);
    preset_n <= 1;

    $display("[%0t] Reset released, uart_tx = %b, uart_rx = %b", $time, intf_uart.uart_tx, intf_uart.uart_rx);
  end

  always @(intf_uart.uart_tx)
    `uvm_info("SALUT_CHK", $sformatf("vif tx is %0b and dut tx is %0b", intf_uart.uart_tx, uart_tx), UVM_NONE)

  
  initial begin
    //se salveaza instantele interfetelor in baza de date UVM
    uvm_config_db#(virtual apb_interface_dut)::set(null, "*", "apb_interface_dut", intf_apb);
    uvm_config_db#(virtual irq_interface_dut)::set(null, "*", "irq_interface_dut", intf_irq);
    uvm_config_db#(virtual uart_interface_dut)::set(null, "*", "uart_interface_dut", intf_uart);
    //se ruleaza testul dorit
    run_test("test_exemplu");
  end

  // se instantiaza DUT-ul, facandu-se legaturile intre semnalele din modulul de top si semnalele acestuia
  uart_apb_dut DUT(
	.pclk      (clk     ),
  .preset_n  (preset_n),
  .paddr     (paddr   ),
  .psel      (psel    ),
  .penable   (penable ),
  .pwrite    (pwrite  ),
  .pwdata    (pwdata  ),
  .prdata    (prdata  ),
  .pready    (pready  ),
  .uart_rx   (uart_rx ),
  .uart_tx   (uart_tx ),
  .int_o     (int_o   )
  );

endmodule