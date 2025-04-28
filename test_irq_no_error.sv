`include "mediu_verificare.sv"

`ifndef __TEST_IRQ_NO_ERROR
`define __TEST_IRQ_NO_ERROR

class test_irq_no_error extends uvm_test;

  `uvm_component_utils(test_irq_no_error)

  mediu_verificare mediu_verificare;

//constructorul clasei
  function new(string name = "test_irq_no_error", uvm_component parent = null);
    super.new(name, parent);
  endfunction

//instantiem mediul de verificare
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mediu_verificare = mediu_verificare::type_id::create("mediu_verificare", this);
  endfunction

//simulam un trafic normal fara generarea de intreruperi
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `uvm_info("TEST_IRQ_NO_ERROR", "incepe testul fara intreruperi", UVM_LOW)

//scriem cateva date in TX FIFO, dar nu umplem FIFO-ul
    repeat (5) begin
      force mediu_verificare.agent_apb.interfata_monitor_apb.paddr = 4'h2;// registru TX
      force mediu_verificare.agent_apb.interfata_monitor_apb.psel = 1'b1;
      force mediu_verificare.agent_apb.interfata_monitor_apb.penable = 1'b1;
      force mediu_verificare.agent_apb.interfata_monitor_apb.pwrite = 1'b1;
      force mediu_verificare.agent_apb.interfata_monitor_apb.pwdata = $urandom_range(0, 255);
      #20ns;
    end

//simulam receptia de date fara overrun; primim un pachet si citim imediat din RX
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b0;// bit de start
    #50ns;
    force mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx = 1'b1;// date valide
    #100ns;
    release mediu_verificare.agent_irq.interfata_monitor_irq.uart_rx;

//simulam citirea datelor receptionate pentru a evita suprascrierea
    force mediu_verificare.agent_apb.interfata_monitor_apb.paddr = 4'h3;// registru RX
    force mediu_verificare.agent_apb.interfata_monitor_apb.psel = 1'b1;
    force mediu_verificare.agent_apb.interfata_monitor_apb.penable = 1'b1;
    force mediu_verificare.agent_apb.interfata_monitor_apb.pwrite = 1'b0;// operatie de citire
    #20ns;

    release mediu_verificare.agent_apb.interfata_monitor_apb.paddr;
    release mediu_verificare.agent_apb.interfata_monitor_apb.psel;
    release mediu_verificare.agent_apb.interfata_monitor_apb.penable;
    release mediu_verificare.agent_apb.interfata_monitor_apb.pwrite;
    release mediu_verificare.agent_apb.interfata_monitor_apb.pwdata;

    `uvm_info("TEST_IRQ_NO_ERROR", "testul s-a terminat fara erori", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass

`endif
