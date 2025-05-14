`ifndef __apb_intf
`define __apb_intf
`include "uvm_macros.svh"
import uvm_pkg::*;

interface apb_interface_dut;
  logic          pclk;      // Clock
  logic          preset_n;  // Active-low reset
  logic          psel;      // Peripheral select
  logic          penable;   // Enable signal
  logic [3:0]    paddr;     // Address bus
  logic          pwrite;    // Write enable
  logic [7:0]    pwdata;    // Write data bus
  logic [7:0]    prdata;    // Read data bus
  logic          pready;    // Ready signal
  logic          pslverr;   // Slave error signal signal

      
//ASERTII
  // psel nu poate fi activ fara pready  
  property psel_without_pready;
    @(posedge pclk) disable iff (!preset_n)
    psel |-> ##[1:$] pready;
  endproperty

  assert_psel_without_pready: assert property (psel_without_pready)
    else `uvm_error("apb_INTERFACE", "psel a fost activ fara ca pready sa fie setat");

  // penable trebuie sa fie activ doar dupa psel  
  property penable_after_psel;
    @(posedge pclk) disable iff (!preset_n)
    penable |-> psel;
  endproperty

  assert_penable_after_psel: assert property (penable_after_psel)
    else `uvm_error("apb_INTERFACE", "penable a fost activ fara ca psel sa fie setat inainte");

  // Adresa nu trebuie sa se schimbe in timpul tranzactiei  
  property stable_address;
    @(posedge pclk) disable iff (!preset_n)
    psel && penable |-> $stable(paddr);
  endproperty

  assert_stable_address: assert property (stable_address)
    else `uvm_error("apb_INTERFACE", "Adresa s-a schimbat in timpul unei tranzactii active");

  // pwdata nu trebuie sa se schimbe in timpul tranzactiei de scriere  
  property stable_pwdata;
    @(posedge pclk) disable iff (!preset_n)
    (psel && penable && pwrite) |-> $stable(pwdata);
  endproperty

  assert_stable_pwdata: assert property (stable_pwdata)
    else `uvm_error("apb_INTERFACE", "pwdata s-a schimbat in timpul unei tranzactii de scriere");   

endinterface

`endif