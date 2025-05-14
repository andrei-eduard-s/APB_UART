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

  bit enable;
  uart_config p_uart_cfg;

  bit [7:0] tx_fifo[0:15];
  int fifo_wr_ptr;
  int fifo_rd_ptr;
  int fifo_count;

  logic [7:0] reg_uart_config;  // addr 0x00
  logic [7:0] reg_data_tx;      // addr 0x02 (W)
  logic [7:0] reg_data_rx;      // addr 0x03 (R)
  logic [7:0] reg_status;       // addr 0x04 (R)

  bit [7:0] rx_reg;
  bit rx_valid;

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

    if (!uvm_config_db#(uart_config)::get(this, "", "uart_config", p_uart_cfg))
      `uvm_fatal("NOCFG", "Failed to get UART config from config DB")

    fifo_wr_ptr = 0;
    fifo_rd_ptr = 0;
    fifo_count  = 0;

    reg_uart_config = 8'h00;
    reg_data_tx     = 8'h00;
    reg_data_rx     = 8'h00;
    reg_status      = 8'h01;

    rx_reg   = 8'h00;
    rx_valid = 0;
  endfunction

  function void write_apb(input tranzactie_apb tranzactie_noua_apb);
    `uvm_info("SCOREBOARD", "Tranzactie APB primita:\n", UVM_LOW)
    tranzactie_noua_apb.afiseaza_informatia_tranzactiei();

    tranzactie_venita_de_la_apb = tranzactie_noua_apb.copy();

    if (tranzactie_venita_de_la_apb.pwrite == 1) begin  // scriere
      case (tranzactie_venita_de_la_apb.paddr)
        8'h00: begin
          reg_uart_config = tranzactie_venita_de_la_apb.pdata;
          p_uart_cfg.decode_uart_config(reg_uart_config);
        end
        8'h02: begin
          if (fifo_count < 16) begin
            reg_data_tx = tranzactie_venita_de_la_apb.pdata;
            tx_fifo[fifo_wr_ptr] = reg_data_tx;
            fifo_wr_ptr = (fifo_wr_ptr + 1) % 16;
            fifo_count++;
            reg_status[0] = (fifo_count == 16);  // Bit 0: FIFO TX plin
          end else begin
            `uvm_info(get_full_name(), "FIFO TX plin - scriere ignorata", UVM_LOW)
          end
        end
        8'h03, 8'h04: `uvm_info(get_full_name(), "REGISTRU READ_ONLY, nu se poate scrie", UVM_LOW)
        default: `uvm_info(get_full_name(), "Adresa incorecta", UVM_LOW)
      endcase
    end else begin  // citire
      case (tranzactie_venita_de_la_apb.paddr)
        8'h00: assert (reg_uart_config == tranzactie_venita_de_la_apb.pdata)
                  else `uvm_error("SCB_APB_ERR", $sformatf("UART_CONFIG mismatch: DUT=%0h, SB=%0h",
                        tranzactie_venita_de_la_apb.pdata, reg_uart_config))
        8'h02: `uvm_info(get_full_name(), "REGISTRU WRITE_ONLY, nu se poate citi", UVM_LOW)
        8'h03: assert (reg_data_rx == tranzactie_venita_de_la_apb.pdata)
                  else `uvm_error("SCB_APB_ERR", $sformatf("DATA_RX mismatch: DUT=%0h, SB=%0h",
                        tranzactie_venita_de_la_apb.pdata, reg_data_rx))
        8'h04: assert (reg_status == tranzactie_venita_de_la_apb.pdata)
                  else `uvm_error("SCB_APB_ERR", $sformatf("STATUS mismatch: DUT=%0h, SB=%0h",
                        tranzactie_venita_de_la_apb.pdata, reg_status))
        default: `uvm_info(get_full_name(), "Adresa incorecta", UVM_LOW)
      endcase
    end
  endfunction : write_apb

  function void write_irq(input tranzactie_irq tranzactie_noua_irq);
    `uvm_info("SCOREBOARD", "Tranzactie IRQ primita:\n", UVM_LOW)
    tranzactie_noua_irq.afiseaza_informatia_tranzactiei();
    tranzactie_venita_de_la_irq = tranzactie_noua_irq.copy();
  endfunction : write_irq

  function void write_uart(input uart_item tranzactie_noua_uart);
    `uvm_info("SCOREBOARD", "Tranzactie UART primita:\n", UVM_LOW)
    tranzactie_noua_uart.afiseaza_informatia_tranzactiei();
    tranzactie_venita_de_la_uart = tranzactie_noua_uart.copy();

    reg_data_tx = tranzactie_venita_de_la_uart.data;

    // Verificare paritate (doar dacă e activă)
    if (reg_uart_config[2] == 0) begin  // paritate activată
      bit parity_calc = ^tranzactie_venita_de_la_uart.data;
      if (reg_uart_config[3] == 0) begin  // paritate pară
        if (parity_calc == tranzactie_venita_de_la_uart.parity)
          reg_status[3] = 0;
        else begin
          `uvm_error("SCB_UART_ERR", $sformatf(
            "Paritate incorecta (par): data=%0b, parity=%0b",
            tranzactie_venita_de_la_uart.data, tranzactie_venita_de_la_uart.parity))
          reg_status[3] = 1;
        end
      end else begin  // paritate impară
        if (parity_calc != tranzactie_venita_de_la_uart.parity)
          reg_status[3] = 0;
        else begin
          `uvm_error("SCB_UART_ERR", $sformatf(
            "Paritate incorecta (impar): data=%0b, parity=%0b",
            tranzactie_venita_de_la_uart.data, tranzactie_venita_de_la_uart.parity))
          reg_status[3] = 1;
        end
      end
    end
  endfunction : write_uart

endclass : scoreboard

`endif
