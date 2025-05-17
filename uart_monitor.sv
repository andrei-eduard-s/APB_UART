
`ifndef __uart_monitor
`define __uart_monitor

class uart_monitor extends uvm_monitor;

  `uvm_component_utils(uart_monitor)

  uart_coverage cvg;

  uvm_analysis_port #(uart_item) item_collected_port;
  uart_item item_collected_rx;
  uart_item item_collected_tx;

  int delay_rx;
  int delay_tx;

  virtual interface uart_interface_dut uart_vif;
  uart_config uart_cfg;
  string agent_name;

  function new(string name = "uart_monitor", uvm_component parent);
    super.new(name, parent);
    item_collected_port = new("item_collected_port", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cvg = uart_coverage::type_id::create("cvg", this);
    item_collected_rx = uart_item::type_id::create("item_collected_rx", this);
    item_collected_tx = uart_item::type_id::create("item_collected_tx", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction : connect_phase

  task run_phase(uvm_phase phase);
    `uvm_info(get_type_name(), "Start Running", UVM_LOW)
    fork
      forever collect_item_rx;
      forever collect_item_tx;
    join
  endtask : run_phase


  task collect_item_rx();

    //capture delay
    delay_rx = 0;
    wait(uart_vif.reset_n == 1);
    while (uart_vif.uart_rx == 1) begin
      @(posedge uart_vif.clk_i);
      if (uart_vif.reset_n == 0) delay_rx = 0;
      else begin delay_rx++;
      end
    end
    item_collected_rx.delay = delay_rx;

    //the start bit
    // @(posedge uart_vif.clk_i);
    // Capture data bits
    for (int i = 0; i < uart_cfg.data_size; i++) begin
      @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
      item_collected_rx.data[i] = uart_vif.uart_rx;
    end

    // Capture parity bit
    @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    item_collected_rx.parity = uart_vif.uart_rx;

    // Capture stop bit(s)
    repeat (uart_cfg.stop_bits_number) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    assert (uart_vif.uart_rx == 1);

    item_collected_rx.afiseaza_informatia_tranzactiei();
    item_collected_port.write(item_collected_rx);  // Send transaction to analysis port

    cvg.rx_data_cp.sample(item_collected_rx.data, item_collected_rx.delay);

  endtask : collect_item_rx

  task collect_item_tx();

    //capture delay
    delay_tx = 0;

    wait(uart_vif.reset_n == 1);
    while (uart_vif.uart_tx == 1) begin
      @(posedge uart_vif.clk_i);
      if (uart_vif.reset_n == 0) delay_tx = 0;
      else begin delay_tx++;
      end
    end
    item_collected_tx.delay = delay_tx;

    //the start bit
    // @(posedge uart_vif.clk_i);
    // Capture data bits
    for (int i = 0; i < uart_cfg.data_size; i++) begin
      @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
      item_collected_tx.data[i] = uart_vif.uart_tx;
    end

    // Capture parity bit
    @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    item_collected_tx.parity = uart_vif.uart_tx;

    // Capture stop bit(s)
    repeat (uart_cfg.stop_bits_number) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    assert (uart_vif.uart_tx == 1);

    item_collected_tx.afiseaza_informatia_tranzactiei();
    `uvm_info("UART_MONITOR", "S-a colectat un item de pe linia TX.", UVM_NONE)
    item_collected_port.write(item_collected_tx);  // Send transaction to analysis port

    cvg.tx_data_cp.sample(item_collected_tx.data, item_collected_tx.delay);

  endtask : collect_item_tx

endclass : uart_monitor

`endif
