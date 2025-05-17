`ifndef __uart_interface_dut
`define __uart_interface_dut

import uvm_pkg::*; 
`include "uvm_macros.svh"

interface uart_interface_dut;
  logic clk_i;        // Clock principal
  logic reset_n;      // Reset activ pe 0
  logic uart_tx;      // Linie de transmisie UART (output)
  logic uart_rx;      // Linie de receptie UART (input)

  // Semnalul uart_tx trebuie sa fie HIGH (idle) dupa reset
  property uart_tx_idle_after_reset;
    @(posedge clk_i) disable iff (!reset_n)
    $rose(reset_n) |-> (uart_tx === 1'b1);
  endproperty

  assert_uart_tx_idle_after_reset: assert property (uart_tx_idle_after_reset)
    else `uvm_error("UART_INTERFACE", "uart_tx nu este in idle dupa reset!");

  // Semnalul uart_rx trebuie sa fie HIGH (idle) dupa reset
  property uart_rx_idle_after_reset;
    @(posedge clk_i) disable iff (!reset_n)
    $rose(reset_n) |-> (uart_rx === 1'b1);
  endproperty

  assert_uart_rx_idle_after_reset: assert property (uart_rx_idle_after_reset)
    else `uvm_error("UART_INTERFACE", "uart_rx nu este in idle dupa reset!");

   // uart_tx trebuie sa inceapa transmisia cu un bit de start (0)
   property uart_tx_start_bit;
     @(posedge clk_i) disable iff (!reset_n)
     (uart_tx === 1'b0) |-> ##1 (uart_tx !== 1'b0);
   endproperty

   assert_uart_tx_start_bit: assert property (uart_tx_start_bit)
     else `uvm_error("UART_INTERFACE", "uart_tx nu a inceput cu bitul de start (0)");

   // uart_rx trebuie sa inceapa receptia cu un bit de start (0)
   property uart_rx_start_bit;
     @(posedge clk_i) disable iff (!reset_n)
     (uart_rx === 1'b0) |-> ##1 (uart_rx !== 1'b0);
   endproperty

   assert_uart_rx_start_bit: assert property (uart_rx_start_bit)
     else `uvm_error("UART_INTERFACE", "uart_rx nu a inceput cu bitul de start (0)");

endinterface

`endif
