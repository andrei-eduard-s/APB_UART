`include "mediu_verificare.sv"

`ifndef __TEST_IRQ_RX_OVERRUN
`define __TEST_IRQ_RX_OVERRUN

class test_irq_rx_overrun extends uvm_test;

  `uvm_component_utils(test_irq_rx_overrun)

  mediu_verificare mediu_verificare;

//constructorul clasei
  function new(string name = "test_irq_rx_overrun", uvm_component parent = null);
    super.new(name, parent);
  endfunction

//instantiem mediul de verificare
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mediu_verificare = mediu_verificare::type_id::create("mediu_verificare", this);
  endfunction

//simulam o situatie de RX_OVERRUN
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `uvm_info("TEST_IRQ_RX_OVERRUN", "incepe testul pentru RX_OVERRUN", UVM_LOW)

    //primim primul pachet pe uart_rx
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b0; // bit de start
    #50ns;
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b1; // date valide

    //nu citim datele, deci reg_status[2] ramane activ

    //primim al doilea pachet => ar trebui sa declanseze overrun
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b0; // bit de start
    #50ns;
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b1; // date valide
    #100ns;

    release mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx;

    `uvm_info("TEST_IRQ_RX_OVERRUN", "testul s-a terminat", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass

`endif
