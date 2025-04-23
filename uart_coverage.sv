`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __uart_coverage
`define __uart_coverage

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului; aceasta clasa este doar de model, si probabil va fi modificata, deoarece in general nu ne intereseaza sa obtinem in simulare toate combinatiile posibile de intrari ale unui DUT
class uart_coverage extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(uart_coverage)
  
  covergroup cvg_uart_rx_values with function sample(bit[7:0] data, bit parity, int delay);
    option.per_instance = 1;

    cp_uart_rx_data: coverpoint data {
      bins min_val = {0};
      bins mid_val[5] = {[1:200]};
      bins big_val = {[200:$]};
    }

    cp_uart_rx_parity: coverpoint parity {
      bins good_parity = {0};
      bins bad_parity = {1};
    }

    cp_uart_rx_delay: coverpoint delay {
      bins min_val = {0};
      bins mid_val[5] = {[1:19]};
      bins big_val = {[20:$]};
    }
    
  endgroup : cvg_uart_rx_values

  covergroup cvg_uart_tx_values with function sample(bit[7:0] data, bit parity, int delay);
    option.per_instance = 1;

    cp_uart_tx_data: coverpoint data {
      bins min_val = {0};
      bins mid_val[5] = {[1:200]};
      bins big_val = {[200:$]};
    }

    cp_uart_tx_parity: coverpoint parity {
      bins good_parity = {0};
      bins bad_parity = {1};
    }

    cp_uart_tx_delay: coverpoint delay {
      bins min_val = {0};
      bins mid_val[5] = {[1:19]};
      bins big_val = {[20:$]};
    }
    
  endgroup : cvg_uart_tx_values
  
  //se creeaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    cvg_uart_rx_values = new();
    cvg_uart_tx_values = new();
  endfunction
  
endclass

`endif