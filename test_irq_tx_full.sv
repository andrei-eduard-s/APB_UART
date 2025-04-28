`include "mediu_verificare.sv"

`ifndef __TEST_IRQ_TX_FULL
`define __TEST_IRQ_TX_FULL

class test_irq_tx_full extends test_exemplu;

  `uvm_component_utils(test_irq_tx_full)

//constructorul clasei
  function new(string name = "test_irq_tx_full", uvm_component parent = null);
    super.new(name, parent);
  endfunction

//simulam o situatie de TX_FULL
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `uvm_info("TEST_IRQ_TX_FULL", "incepe testul pentru TX_FULL", UVM_LOW)

//simulam 16 scrieri succesive in FIFO-ul de transmisie
    repeat (16) begin
//simulam o scriere in registrul de date TX
      force mediu_verificare.agent_apb.interfata_monitor_apb.paddr = 4'h2;//adresa registrului TX
      force mediu_verificare.agent_apb.interfata_monitor_apb.psel = 1'b1;
      force mediu_verificare.agent_apb.interfata_monitor_apb.penable = 1'b1;
      force mediu_verificare.agent_apb.interfata_monitor_apb.pwrite = 1'b1;
      force mediu_verificare.agent_apb.interfata_monitor_apb.pwdata = $urandom_range(0, 255);//date random
      #20ns;
    end

//dupa ce FIFO-ul este plin, asteptam ca intreruperea sa fie activa
    #100ns;

    release mediu_verificare.agent_apb.interfata_monitor_apb.paddr;
    release mediu_verificare.agent_apb.interfata_monitor_apb.psel;
    release mediu_verificare.agent_apb.interfata_monitor_apb.penable;
    release mediu_verificare.agent_apb.interfata_monitor_apb.pwrite;
    release mediu_verificare.agent_apb.interfata_monitor_apb.pwdata;

    `uvm_info("TEST_IRQ_TX_FULL", "testul s-a terminat", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass

`endif
