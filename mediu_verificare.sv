`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __verification_environment
`define __verification_environment

typedef scoreboard;//aceasta este o pre-definire a tipului de data scoreboard folosita pentru a evita erorile aparute in urma faptului ca scoreboardul importa colectorul de coverage "coverage_valori_citite_apb_ref", si colectorul de coverage importa scoreboardul; explicatia in engleza: this is a forward type definition used to solve cross dependency between scoreboard and coverage class
`include "agent_apb.sv"
`include "agent_irq.sv"
`include "uart_agent.sv"
`include "scoreboard.sv"

class mediu_verificare extends uvm_env;
  
  //se adauga mediul de verificare in baza de date
  `uvm_component_utils(mediu_verificare)
  
  
  //se declara interfetele de pe care se vor prelua date
  virtual apb_interface_dut interfata_monitor_apb;
  virtual irq_interface_dut interfata_monitor_irq;
  virtual uart_interface_dut interfata_monitor_uart;

  //se declara configurarea uart
  uart_config uart_cfg;

  //se declara agentii
  agent_apb agent_apb_din_mediu;//agentul activ care furnizeaza stimuli si monitorizeaza interfata de intrare
  agent_irq agent_irq_din_mediu;//agentul pasiv
  uart_agent agent_uart_din_mediu;//agentul activ care furnizeaza stimuli si monitorizeaza interfata de intrare

  //se declara componentele de tip scoreboard (una singura in cazul nostru)
  scoreboard IO_scorboard;
  
  
  //constructorul clasei
  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  
  //se creaza componentele mediului de verificare
  virtual function void build_phase (uvm_phase phase);
    
    //se apeleaza functia build_phase din clasa parinte
    super.build_phase(phase);
    agent_apb_din_mediu = agent_apb::type_id::create("agent_apb_din_mediu", this);
    agent_irq_din_mediu = agent_irq::type_id::create("agent_irq_din_mediu", this);
    agent_uart_din_mediu = uart_agent::type_id::create("agent_uart_din_mediu", this);
    IO_scorboard = scoreboard::type_id::create("IO_scorboard", this);

    //uart config
    uart_cfg = uart_config::type_id::create("uart_cfg", this);
    uvm_config_db#(uart_config)::set(null, "*", "uart_config", uart_cfg);
    
    
  endfunction
  

  //se creaza conexiunile intre componente
  function void connect_phase(uvm_phase phase);
    `uvm_info("MEDIU DE VERIFICARE", "A inceput faza de realizare a conexiunilor", UVM_NONE);
    // se preiau interfetele din baza de date; daca nu se pot prelua interfetele, se va da eroare
    assert(uvm_resource_db#(virtual apb_interface_dut)::read_by_name(
      get_full_name(), "apb_interface_dut", interfata_monitor_apb)) 
      else `uvm_error("MEDIU DE VERIFICARE", "Nu s-a putut prelua din baza de date UVM apb_interface_dut");
    assert(uvm_resource_db#(virtual irq_interface_dut)::read_by_name(
      get_full_name(), "irq_interface_dut", interfata_monitor_irq)) 
      else `uvm_error("MEDIU DE VERIFICARE", "Nu s-a putut prelua din baza de date UVM irq_interface_dut");
	  assert(uvm_resource_db#(virtual uart_interface_dut)::read_by_name(
      get_full_name(), "uart_interface_dut", interfata_monitor_uart)) 
      else `uvm_error("MEDIU DE VERIFICARE", "Nu s-a putut prelua din baza de date UVM apb_interface_dut");
      //se preia configul din baza de date; daca nu se poate prelua configul, se va da eroare
	  assert(uvm_resource_db#(uart_config)::read_by_name(
      get_full_name(), "uart_config", uart_cfg)) 
      else `uvm_error("MEDIU DE VERIFICARE", "Nu s-a putut prelua din baza de date UVM uart_config");
  //conectarea scoreboardului la porturile de date ale agentilor
    agent_apb_din_mediu.de_la_monitor_apb.connect(IO_scorboard.port_pentru_datele_de_la_apb);
    agent_irq_din_mediu.de_la_monitor_irq.connect(IO_scorboard.port_pentru_datele_de_la_irq);
    agent_uart_din_mediu.monitor.item_collected_port.connect(IO_scorboard.port_pentru_datele_de_la_uart);
    `uvm_info("MEDIU DE VERIFICARE", "Faza de realizare a conexiunilor s-a terminat", UVM_HIGH);
  endfunction: connect_phase
  
  task run_phase(uvm_phase phase);
    //phase.raise_objection(this);
    `uvm_info("MEDIU DE VERIFICARE", "Faza de rulare a activitatii mediului de verificare (RUN PHASE) a inceput.", UVM_NONE);
    begin
      //AICI SE POATE SCRIE UN COD DE INITIALIZARE A TRAFICULUI PE INTERFETE DACA ESTE NEVOIE
    end
    //phase.drop_objection(this);
  endtask
  
endclass : mediu_verificare

`endif