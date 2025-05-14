`ifndef __test_apb_write
`define __test_apb_write

`include "uvm_macros.svh"
`include "mediu_verificare.sv"
`include "secventa_apb.sv"
`include "uart_sequence.sv"

class test_apb_write extends uvm_test;

  `uvm_component_utils(test_apb_write)

  function new(string name = "test_apb_write", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  mediu_verificare mediu_de_verificare;
  
  secventa_write apb_seq;
  uart_sequence uart_seq;

  virtual apb_interface_dut vif_apb_dut;
  virtual irq_interface_dut vif_irq_dut;
  virtual uart_interface_dut vif_uart_dut;
  
   function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    this.print();
    uvm_top.print_topology();
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    mediu_de_verificare = mediu_verificare::type_id::create("mediu_de_verificare", this);
    
    if (!uvm_config_db#(virtual apb_interface_dut)::get(this, "", "apb_interface_dut", vif_apb_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala apb_interface_dut pentru a crea vif_apb_dut")
    if (!uvm_config_db#(virtual irq_interface_dut)::get(this, "", "irq_interface_dut", vif_irq_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala irq_interface_dut pentru a crea vif_irq_dut")
    if (!uvm_config_db#(virtual uart_interface_dut)::get(this, "", "uart_interface_dut", vif_uart_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala uart_interface_dut pentru a crea vif_uart_dut")

    apb_seq = secventa_write::type_id::create("apb_seq");
    apb_seq.randomize();

    uart_seq = uart_sequence::type_id::create("uart_seq");
    uart_seq.randomize();  
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    
    `uvm_info("test_apb_write", "real execution begins", UVM_NONE);
    
    //in bucla fork join se pot porni in paralel secventele mediului de verificare
    fork      
      begin 
      `ifdef DEBUG
        $display("va incepe sa ruleze secventa: apb_seq pentru agentul activ agent_apb");
      `endif;
        apb_seq.start(mediu_de_verificare.agent_apb_din_mediu.sequencer_agent_apb_inst0);
      `ifdef DEBUG
        $display("s-a terminat de rulat secventa pentru agentul activ agent_apb");
      `endif;
      end
      begin 
      `ifdef DEBUG
        $display("va incepe sa ruleze secventa: uart_seq pentru agentul activ uart_agent");
      `endif;
        uart_seq.start(mediu_de_verificare.agent_uart_din_mediu.sequencer);
      `ifdef DEBUG
        $display("s-a terminat de rulat secventa pentru agentul activ uart_agent");
      `endif;
      end

    join
    //dupa ce s-au terminat secventele care trimit stimuli DUT-ului, toate semnalele de intrare se pun in valoarea de reset
    @(posedge vif_apb_dut.pclk);
    vif_apb_dut.psel     <= 0;
    vif_apb_dut.penable  <= 0;
    vif_apb_dut.paddr    <= 0;

    vif_uart_dut.uart_tx <= 1;
    vif_uart_dut.uart_rx <= 1;
    #100
    phase.drop_objection(this);
  endtask : run_phase
   
  virtual function void report_phase(uvm_phase phase);
    uvm_report_server svr;
    super.report_phase(phase);
    $display("STDOUT: Valorile de coverage obtinute pentru apb sunt: %3.2f%% ",  		   mediu_de_verificare.agent_apb_din_mediu.monitor_apb_inst0.colector_coverage_apb.stari_apb_cg.get_inst_coverage());
   
    svr = uvm_report_server::get_server();
 
     $display("numar erori: %0d \nnumar warninguri: %0d",svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR), svr.get_severity_count(UVM_WARNING));
      if(svr.get_severity_count(UVM_FATAL) +
         svr.get_severity_count(UVM_ERROR)>0 +
       svr.get_severity_count(UVM_WARNING) > 0) 
		begin
     			`uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
     			`uvm_info(get_type_name(), "----            TEST FAIL          ----", UVM_NONE)
     			`uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
    		end
    	else 
		begin
     			`uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
     			`uvm_info(get_type_name(), "----           TEST PASS           ----", UVM_NONE)
     			`uvm_info(get_type_name(), "---------------------------------------", UVM_NONE)
    		end

        $finish();
  	endfunction 
endclass

`endif


