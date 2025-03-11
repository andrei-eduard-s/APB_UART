`ifndef __uart_interface_dut
`define __uart_interface_dut

import uvm_pkg::*; 
`include "uvm_macros.svh"

interface uart_interface_dut;
  logic clk_i;        // Clock principal
  logic reset_n;      // Reset activ pe 0
  logic uart_tx;      // Linie de transmisie UART (output)
  logic uart_rx;      // Linie de receptie UART (input)


endinterface

`endif
