`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __irq_coverage_collector
`define __irq_coverage_collector

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului; aceasta clasa este doar de model, si probabil va fi modificata, deoarece in general nu ne intereseaza sa obtinem in simulare toate combinatiile posibile de intrari ale unui DUT
class coverage_irq extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(coverage_irq)
  
  //se declara pointerul catre monitorul care da datele asupra carora se vor face masuratorile de coverage
  monitor_irq p_monitor;
  
  covergroup stari_irq_cg;
    option.per_instance = 1;
    coverpoint p_monitor.starea_preluata_a_irq.irq;
  endgroup
  
  //se creeaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    $cast(p_monitor, parent);//with the use of $cast, type check will occur during runtime
    stari_irq_cg = new();
  endfunction
  
endclass


`endif