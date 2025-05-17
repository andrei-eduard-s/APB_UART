`ifndef __test_uart_config
`define __test_uart_config 


`include "test_exemplu.sv"

class test_uart_config extends test_base;

  `uvm_component_utils(test_uart_config)

  //constructorul clasei

  function new(string name = "test_uart_config", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    phase.raise_objection(this);

    apb_write(.paddr(0), .pdata({$urandom_range(63, 0), 'b11}));
    uart_seq.start(mediu_de_verificare.agent_uart_din_mediu.sequencer);
    #100ns;

    apb_write(.paddr(0), .pdata({$urandom_range(63, 0), 'b10}));
    uart_seq.start(mediu_de_verificare.agent_uart_din_mediu.sequencer);
    #100ns;

    apb_write(.paddr(0), .pdata({$urandom_range(63, 0), 'b01}));
    uart_seq.start(mediu_de_verificare.agent_uart_din_mediu.sequencer);
    #100ns;

    // apb_write(.paddr(0), .pdata({$urandom_range(63, 0), 'b00}));
    // uart_seq.start(mediu_de_verificare.agent_uart_din_mediu.sequencer);
    // #100ns;

    phase.drop_objection(this);

  endtask : run_phase

endclass : test_uart_config

`endif
