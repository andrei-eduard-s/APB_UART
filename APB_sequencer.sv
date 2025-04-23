`include "uvm_macros.svh"
import uvm_pkg::*;

class apb_sequencer extends uvm_sequencer #(tranzactie_apb);
    `uvm_component_utils(apb_sequencer)

    function new(string name = "apb_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction
endclass