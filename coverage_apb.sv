`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __apb_coverage_collector
`define __apb_coverage_collector

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului;
  class coverage_apb extends uvm_component;
  //componenta se adauga in baza de date
  `uvm_component_utils(coverage_apb)
  
  //se declara pointerul catre monitorul care da datele asupra carora se vor face masuratorile de coverage
  monitor_apb p_monitor;
  
  covergroup stari_apb_cg;
    option.per_instance = 1;
    addr_cp: coverpoint p_monitor.starea_preluata_a_apb.paddr{
        bins data_tx     = {0};
        bins data_rx     = {2};
        bins status      = {3};
      	bins uart_config = {4};
		    bins other_addresses = default;
    }
	
	  delay_cp: coverpoint p_monitor.starea_preluata_a_apb.delay{
        bins without_delay = {0};
        bins small_delay   = {[1:5]}; 
      	bins large_delay   = {[6:10]};
		    bins other_delays  = {[11:$]};
    }

    perror_cp: coverpoint p_monitor.starea_preluata_a_apb.perror{
        bins low  = {0};
        bins high = {1};
    }

    pwrite_cp:  coverpoint p_monitor.starea_preluata_a_apb.pwrite;

    coverpoint p_monitor.starea_preluata_a_apb.pdata{
      bins low  = {0};
      bins data_ranges[3] = {[1:254]};
      bins maximum = {255};
    }

    cross_addr_cp_pwrite_cp:  cross addr_cp, pwrite_cp ;
    //TODO eroare sintaxa 
    // cross_addr_cp_perror_cp:  cross addr_cp, perror_cp {
    //  bins illegal_combination = binsof(addr_cp.data_tx     ) && binsof(perror_cp.high);
    //  bins illegal_combination = binsof(addr_cp.data_rx     ) && binsof(perror_cp.high);
    //  bins illegal_combination = binsof(addr_cp.status      ) && binsof(perror_cp.high);
    //  bins illegal_combination = binsof(addr_cp.uart_config ) && binsof(perror_cp.high);
    //}

  endgroup
  
  //se creeaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    $cast(p_monitor, parent);//with the use of $cast, type check will occur during runtime
    stari_apb_cg = new();
  endfunction
  
endclass


`endif