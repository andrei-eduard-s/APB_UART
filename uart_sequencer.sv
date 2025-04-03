`ifndef __uart_sequencer
`define __uart_sequencer

class uart_sequencer extends uvm_sequencer #(uart_item);

    `uvm_component_utils(uart_sequencer)

    function new(string name = "uart_sequencer", uvm_component parent);
    super.new(name, parent);
    endfunction : new

endclass : uart_sequencer

`endif