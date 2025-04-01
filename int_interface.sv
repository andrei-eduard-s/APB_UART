`ifndef __irq_interface_dut
`define __irq_interface_dut

import uvm_pkg::*; 
`include "uvm_macros.svh"

interface irq_interface_dut;
  logic         clk_i;       // Clock principal
  logic         reset_n;     // Reset activ pe 0
  logic [2:0]   int_o;       // Semnal de intrerupere global (output)
  //logic [3:0] irq_type; // Codul intreruperii active

// Asertie: Semnalul int_o trebuie sa fie 0 dupa reset
  property irq_reset_state;
    @(posedge clk_i) disable iff (!reset_n)
    $rose(reset_n) |-> (int_o === 3'b000);
  endproperty

  assert_irq_reset_state: assert property (irq_reset_state)
    else `uvm_error("IRQ_INTERFACE", "int_o nu este 0 dupa reset!");

endinterface

`endif
