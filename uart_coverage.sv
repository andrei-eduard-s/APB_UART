`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __uart_coverage
`define __uart_coverage

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului; aceasta clasa este doar de model, si probabil va fi modificata, deoarece in general nu ne intereseaza sa obtinem in simulare toate combinatiile posibile de intrari ale unui DUT
class uart_coverage extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(uart_coverage)
  
  covergroup rx_data_cp with function sample(bit[7:0] data, int delay);
    option.per_instance = 1;

    uart_rx_data: coverpoint data {
      bins min_val    = {0};
      bins mid_val[5] = {[1:254]};
      bins max_val    = {255};
    }

    uart_rx_delay: coverpoint delay {
      bins min_val    = {0};
      bins mid_val[5] = {[1:19]};
      bins max_val    = {20};
    }
    
  endgroup : rx_data_cp

  covergroup tx_data_cp with function sample(bit[7:0] data, int delay);
    option.per_instance = 1;

    uart_tx_data: coverpoint data {
      bins min_val    = {0};
      bins mid_val[5] = {[1:254]};
      bins max_val    = {255};
    }

    uart_tx_delay: coverpoint delay {
      bins min_val    = {0};
      bins mid_val[5] = {[1:19]};
      bins max_val    = {20};
    }
    
  endgroup : tx_data_cp

  covergroup frame_format_cp with function sample(bit[1:0] data_size, bit parity_inctive, bit parity_type, bit stop_bits_number);
    option.per_instance = 1;

    uart_data_size: coverpoint data_size {
      bins eight_bit = {'b11};
      bins seven_bit = {'b10};
      bins six_bit   = {'b01};
      bins five_bit  = {'b00};
    }

    uart_parity_inactive: coverpoint parity_inctive {
      bins active   = {0};
      bins inactive = {1};
    }

    uart_parity_type: coverpoint parity_type {
      bins good_parity = {0};
      bins bad_parity  = {1};
    }

    uart_stop_bits_number: coverpoint stop_bits_number {
      bins one_bit = {0};
      bins two_bit = {1};
    }

    cross uart_data_size, uart_parity_inactive;
    cross uart_data_size, uart_parity_type;
    cross uart_data_size, uart_stop_bits_number;
    cross uart_parity_inactive, uart_parity_type;

  endgroup : frame_format_cp

  //covergroup baud_rate_cp TODO alin
  
  //se creeaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    rx_data_cp = new();
    tx_data_cp = new();
    frame_format_cp = new();
  endfunction
  
endclass

`endif