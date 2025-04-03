//====================
//------SEQ_BASE------
//====================
`define __uart_seq_base
`ifndef __uart_seq_base

class uart_seq_base extends uvm_sequence #(uart_item);

  `uvm_object_utils(uart_seq_base)

  uart_item seq_item;

  rand bit [`DATA_SIZE-1:0] data;
  rand int delay;

  function new(string name = "uart_seq_base");
    super.new(name);
  endfunction : new

  virtual task body();
    `uvm_do(seq_item)
  endtask : body

  virtual task post_body();
    `uvm_info("SEQ", $sformatf("sequence sent: %s", seq_item.sprit()), UVM_NONE)
  endtask : post_body

endclass : uart_seq_base

`endif

//====================
//-----SEQ_CUSTOM-----
//====================
`define __uart_seq_custom
`ifndef __uart_seq_custom

class uart_seq_custom extends uart_seq_base;

  `uvm_object_utils(uart_seq_custom)

  function new(string name = "uart_seq_custom");
    super.new(name);
  endfunction : new

  virtual task body();
    `uvm_create(seq_item)
    seq_item.data = this.data;
    seq_item.delay = this.delay;
    `uvm_send(seq_item)
  endtask : body

endclass : uart_seq_custom

`endif