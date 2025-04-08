
`ifndef __uart_monitor
`define __uart_monitor

virtual class uart_monitor extends uvm_monitor;

  `uvm_component_utils(uart_monitor)

  uart_coverage cvg;

  uvm_analysis_port #(uart_item) item_collected_port;
  uart_item item_collected_rx;
  uart_item item_collected_tx;

  virtual interface uart_interface_dut uart_vif;
  string agent_name;

  function new(string name = "uart_monitor", uvm_component parent);
    super.new(name, parent);
    item_collected_port = new("item_collected_port", this);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cvg = uart_coverage::type_id::create("cvg", this)
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
    int delay = 0;
    while(uart_vif.uart_tx == 1) begin
      @(posedge uart_vif.clk_i);
      delay++;
    end
    item_collected_rx.delay = delay;

    // Capture data bits
    for (int i = 0; i < `DATA_SIZE; i++) begin
      repeat (`BAUD_RATE) 
      @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);  
      item_collected_rx.data[i] = uart_vif.uart_rx;
    end

    // Capture parity bit
    repeat((`BAUD_RATE) * (`PARITY_SIZE-1))
    @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    item_collected_rx.parity[i] = uart_vif.uart_rx; //TODO alin vedem daca trebuie modificati la biti de paritate

    // Capture stop bit(s)
    repeat(`BAUD_RATE)
    @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    assert(uart_vif.uart_rx == 1);

    if(uart_vif.reset_n == 1) begin
      `uvm_info("UART_MONITOR", $sformatf("Captured item on RX: %s", item_collected_rx.sprint()), UVM_MEDIUM);
      item_collected_port.write(item_collected_rx);  // Send transaction to analysis port
    end

    cvg.cvg_uart_rx_values.sample();

  endtask : collect_item_rx

  task collect_item_tx();

    //capture delay
    int delay = 0;
    while(uart_vif.uart_tx == 1) begin
      @(posedge uart_vif.clk_i);
      delay++;
    end
    item_collected_tx.delay = delay;

    // Capture data bits
    for (int i = 0; i < `DATA_SIZE; i++) begin
      repeat(`BAUD_RATE) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);  
      item_collected_tx.data[i] = uart_vif.uart_tx;
    end

    // Capture parity bit
    for (int i = 0; i < `PARITY_SIZE; i++) begin
      repeat(`BAUD_RATE) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
      item_collected_tx.parity = uart_vif.uart_tx; //TODO alin vedem daca trebuie modificati la biti de paritate
    end

    // Capture stop bit(s)
    repeat(`BAUD_RATE * (`STOP_BITS))@(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    assert(uart_vif.uart_tx == 1);

    if(uart_vif.reset_n == 1) begin
      `uvm_info("UART_MONITOR", $sformatf("Captured item on TX: %s", item_collected_tx.sprint()), UVM_MEDIUM);
      item_collected_port.write(item_collected_tx);  // Send transaction to analysis port
    end

    cvg.cvg_uart_tx_values.sample();

  endtask : collect_item_tx

endclass : uart_monitor

`endif