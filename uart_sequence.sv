`ifndef __uart_sequence
`define __uart_sequence

class uart_sequence extends uvm_sequence #(uart_item);

  `uvm_object_utils(uart_sequence)

  uart_item seq_item;

  rand bit [7:0] data;
  rand int delay;

  function new(string name = "uart_sequence");
    super.new(name);
  endfunction : new

  virtual task body();
    `uvm_create(seq_item)
    if (!seq_item.randomize() with {
          delay >= 0;
          delay < 20;
        }) begin
      `uvm_error("UART_SEQ", "Randomization failed for delay!")
    end
    seq_item.data = this.data;  // override only data
    `uvm_send(seq_item)
  endtask


  virtual task post_body();
    `uvm_info("UART_SEQ", $sformatf("sequence sent: %s", seq_item.sprint()), UVM_NONE)
  endtask : post_body

endclass : uart_sequence

`endif
