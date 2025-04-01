`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __agent_int
`define __agent_int

//se includ dependentele folosite de agent
typedef class monitor_agent_actuator;//aceasta este o pre-definire a tipului de data monitor_agent_actuator folosita pentru a evita erorile aparute in urma faptului ca monitorul importa colectorul de coverage, si colectorul de coverage importa monitorul; explicatia in engleza: this is a forward type definition used to solve cross dependency between monitor and coverage class
`include "tranzactie_agent_actuator.sv"
`include "monitor_agent_actuator.sv"

class agent_int extends uvm_agent;
  
  `uvm_component_utils (agent_int)//se adauga agentul la baza de date a acestui proiect; de acolo, acelasi agent se va prelua ulterior spre a putea fi folosit
  
  //se instantiaza componenta de monitorizare a agentului
  monitor_agent_actuator monitor_inst;

  //se declara portul de comunicare al agentului cu scoreboardul/mediul de referinta; prin acest port agentul trimite spre verificare datele preluate de la monitor; a se observa ca intre monitor si agent (practic in interiorul agentului) comunicarea se face la nivel de tranzactie
  uvm_analysis_port #(tranzactie_agent_actuator) port_de_la_monitor;

  //se declara constructorul clasei; acesta este un cod standard pentru toate componentele
  function new (string name = "agent_int", uvm_component parent = null);
    super.new (name, parent);
    port_de_la_monitor = new("port_de_la_monitor", this);
  endfunction 
  
  //rularea unui mediu de verificare cuprinde mai multe faze; in faza "build", se "asambleaza" agentul
  virtual function void build_phase (uvm_phase phase);
    
    //se apeleaza functia build_phase din clasa parinte (uvm_agent)
    super.build_phase(phase);
    
    //atat agentii activi, cat si agentii pasivi au nevoie de un monitor 
    monitor_inst = monitor_agent_actuator::type_id::create ("monitor_inst", this);

  endfunction
  
  //rularea unui mediu de verificare cuprinde mai multe faze; in faza "connect", se realizeaza conexiunile intre componente; in cazul agentului, se realizeaza conexiunile intre sub-componentele agentului
  virtual function void connect_phase (uvm_phase phase);
    
    //se apeleaza functia connect_phase din clasa parinte (uvm_agent)
    super.connect_phase(phase);
    
    //se conecteaza portul agentului cu portul de comunicatie al monitorului din agent (monitorul nu poate trimite date in exterior decat prin intermediul agentului din care face parte)
    port_de_la_monitor = monitor_inst.port_date_monitor_actuator;

  endfunction
endclass
`endif
