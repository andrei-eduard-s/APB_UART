`ifndef __monitor_agent_actuator
`define __monitor_agent_actuator

//monitorul care observa semnalul int_o si transmite tranzactii cu valoarea acestuia
class monitor_agent_actuator extends uvm_monitor;

  //monitorul se adauga in baza de date uvm
  `uvm_component_utils(monitor_agent_actuator)

  //port prin care monitorul transmite tranzactiile catre scoreboard sau alte componente
  uvm_analysis_port #(tranzactie_agent_actuator) port_date_monitor_actuator;

  //declaratia interfetei virtuale conectate la semnalele dut-ului
  virtual irq_interface interfata_monitor_actuator;

  //obiectele de tip tranzactie in care se retin datele observate
  tranzactie_agent_actuator tranzactie_curenta, tranzactie_aux;

  //constructorul clasei
  function new(string name = "monitor_agent_actuator", uvm_component parent = null);
    //se apeleaza constructorul clasei de baza
    super.new(name, parent);

    //se creeaza portul de output pentru tranzactii
    port_date_monitor_actuator = new("port_date_monitor_actuator", this);

    //se creeaza obiectele de tip tranzactie
    tranzactie_curenta = tranzactie_agent_actuator::type_id::create("tranzactie_curenta");
    tranzactie_aux     = tranzactie_agent_actuator::type_id::create("tranzactie_aux");
  endfunction

  //in faza build se obtine interfata virtuala din baza de date uvm
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual irq_interface)::get(this, "", "irq_interface", interfata_monitor_actuator))
      `uvm_fatal("MONITOR_AGENT_ACTUATOR", "nu s-a putut accesa interfata monitorului")
  endfunction

  //faza run unde se monitorizeaza semnalul int_o
  virtual task run_phase(uvm_phase phase);
    forever begin
      //sincronizare la front pozitiv de ceas
      @(posedge interfata_monitor_actuator.clk);

      //se preia valoarea semnalului int_o
      tranzactie_curenta.interrupt = interfata_monitor_actuator.int_o;

      //se copiaza tranzactia pentru a fi transmisa mai departe
      tranzactie_aux = tranzactie_curenta.copy();

      //se transmite tranzactia catre portul de analiza
      port_date_monitor_actuator.write(tranzactie_aux);

      //se afiseaza in consola informatia preluata
      `uvm_info("MONITOR_AGENT_ACTUATOR", $sformatf("s-a detectat intrerupere: int_o = %03b", tranzactie_aux.interrupt), UVM_LOW)
    end
  endtask

endclass

`endif
