`ifndef __uart_agent
`define __uart_agent

typedef class uart_monitor;
`include "uart_config.sv"
`include "uart_item.sv"
`include "uart_sequencer.sv"
`include "uart_coverage.sv"
`include "uart_monitor.sv"
`include "uart_driver.sv"

class uart_agent extends uvm_agent;

  `uvm_component_utils(uart_agent)

  //if the agent is active or not
  uvm_active_passive_enum is_active = UVM_ACTIVE;

  //creating instances for main uvc compoments
  uart_monitor monitor;
  uart_driver driver;
  uart_sequencer sequencer;

  string name;
  virtual interface uart_interface_dut uart_vif;
  uart_config uart_cfg;

  function new(string name = "uart_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual uart_interface_dut)::get(this, "", "uart_interface_dut", uart_vif))
      `uvm_fatal("NOVIF", "No virtual interface specified for this agent instance.")

    if (!uvm_config_db#(uart_config)::get(this, "", "uart_config", uart_cfg))
      `uvm_fatal("NOCFG", "No config file specified for this agent instance.")

    monitor = uart_monitor::type_id::create("monitor", this);
    if (is_active == UVM_ACTIVE) begin
      driver = uart_driver::type_id::create("driver", this);
      sequencer = uart_sequencer::type_id::create("sequencer", this);
    end

  endfunction : build_phase

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    monitor.agent_name = this.name;
    monitor.uart_vif   = this.uart_vif;
    monitor.uart_cfg   = this.uart_cfg;

    if (is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
      driver.agent_name = this.name;
      driver.uart_vif   = this.uart_vif;
      driver.uart_cfg   = this.uart_cfg;
    end

  endfunction : connect_phase

endclass : uart_agent

`endif
