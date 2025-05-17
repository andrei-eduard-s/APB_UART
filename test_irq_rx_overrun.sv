`include "mediu_verificare.sv"

`ifndef __TEST_IRQ_RX_OVERRUN
`define __TEST_IRQ_RX_OVERRUN

class test_irq_rx_overrun extends test_exemplu;

  `uvm_component_utils(test_irq_rx_overrun)

//constructorul clasei
  function new(string name = "test_irq_rx_overrun", uvm_component parent = null);
    super.new(name, parent);
  endfunction

//simulam o situatie de RX_OVERRUN
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `uvm_info("TEST_IRQ_RX_OVERRUN", "incepe testul pentru RX_OVERRUN", UVM_LOW)

//primim primul pachet pe uart_rx
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b0;//bit de start
    #50ns;
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b1;//date valide

//nu citim datele, deci reg_status[2] ramane activ

//primim al doilea pachet => ar trebui sa declanseze overrun
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b0;//bit de start
    #50ns;
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b1;//date valide
    #100ns;

    release mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx;

    `uvm_info("TEST_IRQ_RX_OVERRUN", "testul s-a terminat", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass

`endif
