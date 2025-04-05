`include "uvm_macros.svh"
import uvm_pkg::*;

class APB_sequencer extends uvm_sequencer #(tranzactie_APB);
    `uvm_component_utils(APB_sequencer)

    function new(string name = "APB_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction
endclass