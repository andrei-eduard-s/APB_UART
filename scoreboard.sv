`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __scoreboard
`define __scoreboard

`uvm_analysis_imp_decl(_apb)
`uvm_analysis_imp_decl(_uart)
`uvm_analysis_imp_decl(_irq)

class scoreboard extends uvm_scoreboard;

  `uvm_component_utils(scoreboard)

  uvm_analysis_imp_apb #(tranzactie_apb, scoreboard) port_pentru_datele_de_la_apb;
  uvm_analysis_imp_irq #(tranzactie_irq, scoreboard) port_pentru_datele_de_la_irq;
  uvm_analysis_imp_uart #(uart_item, scoreboard) port_pentru_datele_de_la_uart;

  tranzactie_apb tranzactie_venita_de_la_apb;
  tranzactie_irq tranzactie_venita_de_la_irq;
  uart_item tranzactie_venita_de_la_uart;

  //tranzactie_apb    tranzactii_apb[$];
  //tranzactie_irq tranzactii_irq[$];

  bit enable;

  uart_config p_uart_cfg;

  bit [7:0] tx_fifo[0:15];  // Array to mimic the 16-entry TX FIFO
  int fifo_wr_ptr;  // Write pointer for the FIFO
  int fifo_rd_ptr;  // Read pointer for the FIFO
  int fifo_count;  // Number of items in the FIFO

  logic [7:0] reg_data_tx;  // addr 0
  logic [7:0] reg_data_rx;  // addr 2
  logic [7:0] reg_status;  // addr 3
  logic [7:0] reg_uart_config;  // addr 4

  bit [7:0] rx_reg;  // Single register for RX data
  bit rx_valid;  // Flag to indicate if RX data is available



  function new(string name = "scoreboard", uvm_component parent = null);
    super.new(name, parent);
    port_pentru_datele_de_la_apb  = new("pentru_datele_de_la_apb", this);
    port_pentru_datele_de_la_irq  = new("pentru_datele_de_la_irq", this);
    port_pentru_datele_de_la_uart = new("pentru_datele_de_la_uart", this);

    tranzactie_venita_de_la_apb   = new();
    tranzactie_venita_de_la_irq   = new();
    tranzactie_venita_de_la_uart  = new();
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Add initialization code here (e.g., variables, queues, etc.)
    if (!uvm_config_db#(uart_config)::get(this, "", "uart_config", p_uart_cfg))
      `uvm_fatal("NOCFG", "Failed to get UART config from config DB")

    fifo_wr_ptr = 0;  // starts at the beginning of the FIFO
    fifo_rd_ptr = 0;  // (empty) also starts at the beginning
    fifo_count  = 0;  // No items in the FIFO at the start

    reg_data_tx = 0;
    reg_data_rx = 0;
    reg_status = 0; 
    reg_uart_config = 0;

    rx_reg = 0; 
    rx_valid = 0;


  endfunction

  function void write_apb(input tranzactie_apb tranzactie_noua_apb);
  `uvm_info("SCOREBOARD", $sformatf("S-a primit de la agentul apb tranzactia cu informatia:\n"),
            UVM_LOW)

  tranzactie_noua_apb.afiseaza_informatia_tranzactiei();
  $display($sformatf("cand s-au primit date de la apb, enable a fost %d", enable));

  tranzactie_venita_de_la_apb = tranzactie_noua_apb.copy();

  if (tranzactie_venita_de_la_apb.pwrite == 1) begin  // scriere
    case (tranzactie_venita_de_la_apb.paddr)
      0: reg_data_tx = tranzactie_venita_de_la_apb.pdata;
      2: `uvm_info(get_full_name(), "REGISTRU READ_ONLY, nu se poate scrie", UVM_LOW)
      3: `uvm_info(get_full_name(), "REGISTRU READ_ONLY, nu se poate scrie", UVM_LOW)
      4: begin
        reg_uart_config = tranzactie_venita_de_la_apb.pdata;
        p_uart_cfg.decode_uart_config(reg_uart_config);
      end
      default: `uvm_info(get_full_name(), "Adresa incorecta", UVM_LOW)
    endcase
  end else begin  // citire
    case (tranzactie_venita_de_la_apb.paddr)
      0: `uvm_info(get_full_name(), "REGISTRU WRITE_ONLY, nu se poate citi", UVM_LOW)
      2: assert (reg_data_rx == tranzactie_venita_de_la_apb.pdata)
            else `uvm_error("SCB_APB_ERR", $sformatf(
                    "Valoarea prezisa de DUT (apb data): %0h, valoarea din scoreboard (reg data): %0h",
                    tranzactie_venita_de_la_apb.pdata, reg_data_rx))
      3: assert (reg_status == tranzactie_venita_de_la_apb.pdata)
            else `uvm_error("SCB_APB_ERR", $sformatf(
                    "Valoarea prezisa de DUT (apb status): %0h, valoarea din scoreboard (reg status): %0h",
                    tranzactie_venita_de_la_apb.pdata, reg_status))
      4: assert (reg_uart_config == tranzactie_venita_de_la_apb.pdata)
            else `uvm_error("SCB_APB_ERR", $sformatf(
                    "Valoarea prezisa de DUT (apb uart config): %0h, valoarea din scoreboard (reg uart config): %0h",
                    tranzactie_venita_de_la_apb.pdata, reg_uart_config))
      default: `uvm_info(get_full_name(), "Adresa incorecta", UVM_LOW)
    endcase
  end
  // tranzactii_apb.push_back(tranzactie_venita_de_la_apb); // optional queue for history
endfunction : write_apb


  function void write_irq(input tranzactie_irq tranzactie_noua_irq);
    `uvm_info("SCOREBOARD", $sformatf("S-a primit de la agentul irq tranzactia cu informatia:\n"),
              UVM_LOW)
    tranzactie_noua_irq.afiseaza_informatia_tranzactiei();

    tranzactie_venita_de_la_irq = tranzactie_noua_irq.copy();
    //tranzactii_irq.push_back(tranzactie_venita_de_la_irq);
  endfunction : write_irq

  function void write_uart(input uart_item tranzactie_noua_uart);
  `uvm_info("SCOREBOARD", $sformatf("S-a primit de la agentul uart tranzactia cu informatia:\n"),
            UVM_LOW)

  tranzactie_noua_uart.afiseaza_informatia_tranzactiei();
  tranzactie_venita_de_la_uart = tranzactie_noua_uart.copy();

  // Procesam tranzactia UART
  reg_data_tx = tranzactie_venita_de_la_uart.data;

  // Daca avem paritate activata si este para (reg_uart_config[2] = 1 && reg_uart_config[3] = 0)
  if (reg_uart_config[2] == 0 && reg_uart_config[3] == 0) begin
    if (^{tranzactie_venita_de_la_uart.data, tranzactie_venita_de_la_uart.parity} == 0)
      reg_status[3] = 0;
    else begin
      `uvm_error("SCB_UART_ERR", $sformatf(
        "Valoarea de paritate este gresita: %0b pentru data: %0b",
        tranzactie_venita_de_la_uart.parity, ^tranzactie_venita_de_la_uart.data))
      reg_status[3] = 1;
    end
  end

  // Daca paritatea e activata si trebuie sa fie impara (reg_uart_config[3] = 1)
  if (reg_uart_config[2] == 0 && reg_uart_config[3] == 1) begin
    if (^{tranzactie_venita_de_la_uart.data, tranzactie_venita_de_la_uart.parity} == 1)
      reg_status[3] = 0;
    else begin
      `uvm_error("SCB_UART_ERR", $sformatf(
        "Valoarea de paritate este gresita: %0b pentru data: %0b",
        tranzactie_venita_de_la_uart.parity, ^tranzactie_venita_de_la_uart.data))
      reg_status[3] = 1;
    end
  end
endfunction : write_uart


  /*  virtual function void check_phase (uvm_phase phase);
   foreach(tranzactii_irq[i]) begin
      //checker 1
      if (tranzactii_irq[i].irq == 1) begin
        if(tranzactii_irq[i].addr != tranzactii_apb[i].paddr)
          `uvm_error("SCOREBOARD checker 1", $sformatf("IRQ asserted wrong, address on apb is %h and on irq is %h", tranzactii_apb[i].paddr, tranzactii_irq[i].addr))
        else 
          `uvm_info("SCOREBOARD checker 1", "IRQ ASSERTED: OK", UVM_LOW)
      end
      //checker 2
      if((tranzactii_irq[i].addr == tranzactii_apb[i].paddr) && (tranzactii_irq[i].irq == 0))
        `uvm_error("SCOREBOARD checker 2", "IRQ expected but not asserted")
      else 
        `uvm_info("SCOREBOARD checker 2", "IRQ ASSERTED: OK", UVM_LOW)
    end
  endfunction*/
endclass : scoreboard

`endif
