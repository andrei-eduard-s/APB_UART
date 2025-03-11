`ifndef __apb_interface_dut
`define __apb_interface_dut

import uvm_pkg::*; 
`include "uvm_macros.svh"

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
  //logic        pslverr;   // Slave error signal

  // Asertii pentru verificarea protocolului APB
  // TO DO

endinterface

`endif
