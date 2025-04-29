`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __apb_monitor
`define __apb_monitor
//`include "tranzactie_semafoare.sv"

class monitor_apb extends uvm_monitor;
  
  //monitorul se adauga in baza de date UVM
  `uvm_component_utils (monitor_apb) 
  
  //se declara colectorul de coverage care va inregistra valorile semnalelor de pe interfata citite de monitor
  coverage_apb colector_coverage_apb; 
  
  //este creat portul prin care monitorul trimite spre exterior (la noi, informatia este accesata de scoreboard), prin intermediul agentului, tranzactiile extrase din traficul de pe interfata
  uvm_analysis_port #(tranzactie_apb) port_date_monitor_apb;
  
  //declaratia interfetei de unde monitorul isi colecteaza datele
  //virtual interfata_apb interfata_monitor_apb;
  virtual apb_interface_dut interfata_monitor_apb;
  
  tranzactie_apb starea_preluata_a_apb, aux_tr_apb;
  int delay;
  //constructorul clasei
  function new(string name = "monitor_apb", uvm_component parent = null);
    
    //prima data se apeleaza constructorul clasei parinte
    super.new(name, parent);
    
    //se creeaza portul prin care monitorul trimite in exterior, prin intermediul agentului, datele pe care le-a cules din traficul de pe interfata
    port_date_monitor_apb = new("port_date_monitor_apb",this);
    
    //se creeaza colectorul de coverage (la creare, se apeleaza constructorul colectorului de coverage)
    
    colector_coverage_apb = coverage_apb::type_id::create ("colector_coverage_apb", this);
    
    
    //se creeaza obiectul (tranzactia) in care se vor retine datele colectate de pe interfata la fiecare tact de ceas
    starea_preluata_a_apb = tranzactie_apb::type_id::create("date_noi");
    
    aux_tr_apb = tranzactie_apb::type_id::create("datee_noi");
  endfunction
  
  
  //se preia din baza de date interfata la care se va conecta monitorul pentru a citi date, si se "leaga" la interfata pe care deja monitorul o contine
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual apb_interface_dut)::get(this, "", "apb_interface_dut", interfata_monitor_apb))
        `uvm_fatal("MONITOR_apb", "Nu s-a putut accesa interfata monitorului")
  endfunction
        
  
  
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    
    //in faza UVM "connect", se face conexiunea intre pointerul catre monitor din instanta colectorului de coverage a acestui monitor si monitorul insusi 
	colector_coverage_apb.p_monitor = this;
    
  endfunction
  
   virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    forever begin
      delay = 0;
      //asteptam ca datele sa fie valide
      while(interfata_monitor_apb.psel == 0) begin // @(posedge negedge interfata_monitor_apb.pclk iff interfata_monitor_apb.pready == 1)      
        @(negedge interfata_monitor_apb.pclk);
        delay++;
      end

       wait(interfata_monitor_apb.pready)
     // @(negedge interfata_monitor_apb.pclk); 
      //preiau datele de pe interfata de iesire a DUT-ului
      starea_preluata_a_apb.delay = delay;
      starea_preluata_a_apb.paddr  = interfata_monitor_apb.paddr;
      starea_preluata_a_apb.pwrite = interfata_monitor_apb.pwrite;
      
      if(starea_preluata_a_apb.pwrite)
        starea_preluata_a_apb.pdata = interfata_monitor_apb.pwdata;
      else
        starea_preluata_a_apb.pdata = interfata_monitor_apb.prdata;
    
      aux_tr_apb = starea_preluata_a_apb.copy();//nu vreau sa folosesc pointerul starea_preluata_a_apb pentru a trimite datele, deoarece continutul acestuia se schimba, iar scoreboardul va citi alte date 
      
       //tranzactia cuprinzand datele culese de pe interfata se pune la dispozitie pe portul monitorului, daca modulul nu este in reset
      port_date_monitor_apb.write(aux_tr_apb); 
      `uvm_info("MONITOR_APB", $sformatf("S-a receptionat tranzactia cu informatiile:"), UVM_NONE)
      aux_tr_apb.afiseaza_informatia_tranzactiei();
	  
      //se inregistreaza valorile de pe cele doua semnale de iesire
      colector_coverage_apb.stari_apb_cg.sample();
      
	  @(negedge interfata_monitor_apb.pclk); //acest wait il adaug deoarece uneori o tranzactie este interpretata a fi doua tranzactii identice back to back (validul este citit ca fiind 1 pe doua fronturi consecutive de ceas); in implementarea curenta nu se poate sa vina doua tranzactii back to back
    //????? 
     //functie delay  
    end//forever begin
  endtask
  
  
endclass: monitor_apb

`endif