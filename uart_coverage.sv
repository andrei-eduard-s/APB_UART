`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __uart_coverage
`define __uart_coverage

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului; aceasta clasa este doar de model, si probabil va fi modificata, deoarece in general nu ne intereseaza sa obtinem in simulare toate combinatiile posibile de intrari ale unui DUT
class uart_coverage extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(coverage_apb)
  
  //se declara pointerul catre monitorul care da datele asupra carora se vor face masuratorile de coverage
  uart_monitor p_monitor;
  
  covergroup cvg_uart_rx_values;
    option.per_instance = 1;

    coverpoint p_monitor.collect_item_rx.data {
      bins min_val = {0};
      bins mid_val[5] = {[1:200]};
      bins big_val = {[200:$]};
    }

    coverpoint p_monitor.collect_item_rx.parity {
      bins good_parity = {0};
      bins bad_parity = {1};
    }

    coverpoint p_monitor.collect_item_rx.stop {
      bins one_bit = {0};
      bins two_bits = {1};
    }

    coverpoint p_monitor.collect_item_rx.delay {
      bins min_val = {0};
      bins mid_val[5] = {[1:19]};
      bins big_val = {[20:$]};
    }
    
  endgroup : cvg_uart_rx_values

  covergroup cvg_uart_tx_values;
    option.per_instance = 1;

    coverpoint p_monitor.collect_item_tx.data {
      bins min_val = {0};
      bins mid_val[5] = {[1:200]};
      bins big_val = {[200:$]};
    }

    coverpoint p_monitor.collect_item_tx.parity {
      bins good_parity = {0};
      bins bad_parity = {1};
    }

    coverpoint p_monitor.collect_item_tx.stop {
      bins one_bit = {0};
      bins two_bits = {1};
    }

    coverpoint p_monitor.collect_item_tx.delay {
      bins min_val = {0};
      bins mid_val[5] = {[1:19]};
      bins big_val = {[20:$]};
    }
    
  endgroup : cvg_uart_rx_values
  
  //se creeaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    $cast(p_monitor, parent);//with the use of $cast, type check will occur during runtime
    cvg_uart_rx_values = new();
    cvg_uart_tx_values = new();
  endfunction
  
endclass


`endif