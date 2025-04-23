`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __irq_monitor
`define __irq_monitor
//`include "tranzactie_semafoare.sv"

class monitor_irq extends uvm_monitor;
  
  //monitorul se adauga in baza de date UVM
  `uvm_component_utils (monitor_irq) 
  
  //se declara colectorul de coverage care va inregistra valorile semnalelor de pe interfata citite de monitor
  coverage_irq colector_coverage_irq; 
  
  //este creat portul prin care monitorul trimite spre exterior (la noi, informatia este accesata de scoreboard), prin intermediul agentului, tranzactiile extrase din traficul de pe interfata
  uvm_analysis_port #(tranzactie_irq) port_date_monitor_irq;
  
  //declaratia interfetei de unde monitorul isi colecteaza datele
  //virtual interfata_irq interfata_monitor_irq;
  virtual irq_interface_dut interfata_monitor_irq;
  
  tranzactie_irq starea_preluata_a_irq, aux_tr_irq;
  
  //constructorul clasei
  function new(string name = "monitor_irq", uvm_component parent = null);
    
    //prima data se apeleaza constructorul clasei parinte
    super.new(name, parent);
    
    //se creeaza portul prin care monitorul trimite in exterior, prin intermediul agentului, datele pe care le-a cules din traficul de pe interfata
    port_date_monitor_irq = new("port_date_monitor_irq",this);
    
    //se creeaza colectorul de coverage (la creare, se apeleaza constructorul colectorului de coverage)
    
    colector_coverage_irq = coverage_irq::type_id::create ("colector_coverage_irq", this);
    
    
    //se creeaza obiectul (tranzactia) in care se vor retine datele colectate de pe interfata la fiecare tact de ceas
    starea_preluata_a_irq = tranzactie_irq::type_id::create("date_noi");
    
    aux_tr_irq = tranzactie_irq::type_id::create("datee_noi");
  endfunction
  
  
  //se preia din baza de date interfata la care se va conecta monitorul pentru a citi date, si se "leaga" la interfata pe care deja monitorul o contine
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual irq_interface_dut)::get(this, "", "irq_interface_dut", interfata_monitor_irq))
        `uvm_fatal("MONITOR_irq", "Nu s-a putut accesa interfata monitorului")
  endfunction
        
  
  
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    
    //in faza UVM "connect", se face conexiunea intre pointerul catre monitor din instanta colectorului de coverage a acestui monitor si monitorul insusi 
	colector_coverage_irq.p_monitor = this;
    
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    forever begin
      
      wait(interfata_monitor_irq.int_o); 
      starea_preluata_a_irq.irq = interfata_monitor_irq.int_o;

      aux_tr_irq = starea_preluata_a_irq.copy();//nu vreau sa folosesc pointerul starea_preluata_a_irq pentru a trimite datele, deoarece continutul acestuia se schimba, iar scoreboardul va citi alte date 
      
       //tranzactia cuprinzand datele culese de pe interfata se pune la dispozitie pe portul monitorului, daca modulul nu este in reset
      port_date_monitor_irq.write(aux_tr_irq); 
      `uvm_info("MONITOR_irq", $sformatf("S-a receptionat tranzactia cu informatiile:"), UVM_NONE)
      aux_tr_irq.afiseaza_informatia_tranzactiei();
	  
      //se inregistreaza valorile de pe cele doua semnale de iesire
      colector_coverage_irq.stari_irq_cg.sample();
      
	  @(negedge interfata_monitor_irq.clk); //acest wait il adaug deoarece uneori o tranzactie este interpretata a fi doua tranzactii identice back to back (validul este citit ca fiind 1 pe doua fronturi consecutive de ceas); in implementarea curenta nu se poate sa vina doua tranzactii back to back
      
      
    end//forever begin
  endtask
  
  
endclass: monitor_irq

`endif