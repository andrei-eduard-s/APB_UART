`ifndef __uart_driver
`define __uart_driver

class uart_driver extends uvm_driver #(uart_item);
  
  `uvm_component_utils(uart_driver)
  
  virtual interface uart_interface_dut uart_vif;
  uart_config uart_cfg;
  string agent_name;
  
  function new(string name = "uart_driver", uvm_component parent);
    super.new(name, parent);
  endfunction : new
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      forever begin
        seq_item_port.get_next_item(req);
        drive_item(req);
        `uvm_info("ITEM_DRIVE", $sformatf("Driving UART item:\n%s", req.sprint()), UVM_LOW)
        seq_item_port.item_done();
      end
      forever reset_signals;
    join

  endtask : run_phase
  
  task drive_item(uart_item item_driven);

    void'(this.begin_tr(item_driven, "item_driven"));

    //wait for the reset to be inactive, if it is (or the delay)
    fork
    wait(vif.reset_n == 1);
    repeat(item_driven.delay) @(posedge uart_vif.clk_i);
    join
    //begin transaction by lowering the interface signals
    repeat(`BAUD_RATE) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    uart_vif.uart_tx <= 0;
    //transmit data
    for (int i = 0; i < uart_cfg.data_size; i++) begin
      repeat(`BAUD_RATE) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
      uart_vif.uart_tx <= item_driven.data[i];
    end
    //parity bits
    repeat(`BAUD_RATE) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    uart_vif.uart_tx <= item_driven.parity; 

    //stop bit
    repeat(`BAUD_RATE *(uart_cfg.stop_bits_number)) @(posedge uart_vif.clk_i iff uart_vif.reset_n == 1);
    uart_vif.uart_tx <= 1'b1; 

    this.end_tr(item_driven);

  endtask : drive_item


  task reset_signals();
  //initialize signals
  uart_vif.uart_tx <= 1;
  //then reset them at every reset_n occurence
  @(negedge uart_vif.reset_n);

  endtask : reset_signals
  
  
endclass : uart_driver

`endif