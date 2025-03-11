`ifndef __irq_interface_dut
`define __irq_interface_dut

import uvm_pkg::*; 
`include "uvm_macros.svh"

interface irq_interface_dut;
  logic         clk_i;       // Clock principal
  logic         reset_n;     // Reset activ pe 0
  logic [2:0]   int_o;       // Semnal de intrerupere global (output)
  //logic [3:0] irq_type; // Codul intreruperii active


endinterface

`endif
