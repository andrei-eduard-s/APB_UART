`ifndef __uart_agent
`define __uart_agent

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

  function new(string name = "uart_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual uart_vif)::get(this, "", "uart_vif", uart_vif))
      `uvm_fatal("NOVIF", "No virtual interface specified for this agent instance.")

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

    if (is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
      driver.agent_name = this.name;
      driver.uart_vif   = this.uart_vif;
    end

  endfunction : connect_phase

endclass : uart_agent

`endif
