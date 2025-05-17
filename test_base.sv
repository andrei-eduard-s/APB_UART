`ifndef __test_base
`define __test_base

`include "uvm_macros.svh"
//se includ fisierele la care testul trebuie sa aiba acces
`include "mediu_verificare.sv"
`include "secventa_apb.sv"
`include "secventa_apb_fixa.sv"
`include "uart_sequence.sv"

class test_base extends uvm_test;

  `uvm_component_utils(test_base)
  
  //se declara constructorul testului
  function new(string name = "test_base", uvm_component parent=null);
    super.new(name, parent);
  endfunction
  
  //se instantiaza mediul de verificare
  mediu_verificare mediu_de_verificare;
  
  //se instantiaza secventa folosita de agent_buton si agent_actuator
  secventa_apb apb_seq;
  secventa_apb_fixa apb_f_seq;
  uart_sequence uart_seq;
  
  //se instantiaza interfetele virtuale ale mediului de verificare; acestea vor fi ulterior corelate cu interfetele reale definite in fisierele interfata_intrari_dut si interfata_semafoare

  virtual apb_interface_dut vif_apb_dut;
  virtual irq_interface_dut vif_irq_dut;
  virtual uart_interface_dut vif_uart_dut;

  extern virtual task apb_write(bit[2:0] paddr, bit[7:0] pdata);
  
  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    this.print();
    uvm_top.print_topology();
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    //se creaza mediul de verificare declarat mai sus
    mediu_de_verificare = mediu_verificare::type_id::create("mediu_de_verificare", this);
    
    //Get virtual IF handle from top_level and pass it to everything in env level
    if (!uvm_config_db#(virtual apb_interface_dut)::get(this, "", "apb_interface_dut", vif_apb_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala apb_interface_dut pentru a crea vif_apb_dut")
    if (!uvm_config_db#(virtual irq_interface_dut)::get(this, "", "irq_interface_dut", vif_irq_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala irq_interface_dut pentru a crea vif_irq_dut")
    if (!uvm_config_db#(virtual uart_interface_dut)::get(this, "", "uart_interface_dut", vif_uart_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala uart_interface_dut pentru a crea vif_uart_dut")

    apb_seq = secventa_apb::type_id::create("apb_seq");
    apb_seq.randomize();

    apb_f_seq = secventa_apb_fixa::type_id::create("apb_f_seq");

    uart_seq = uart_sequence::type_id::create("uart_seq");
    uart_seq.randomize();
    
  endfunction
  
  
  //in aceasta faza, care se desfasoara dupa faza de run in care se intampla actiunea propriu-zisa in mediul de verificare, afisam valorile de coverage
  virtual function void report_phase(uvm_phase phase);
    uvm_report_server svr;
    super.report_phase(phase);
    $display("STDOUT: Valorile de coverage obtinute pentru apb sunt: %3.2f%% ", mediu_de_verificare.agent_apb_din_mediu.monitor_apb_inst0.colector_coverage_apb.stari_apb_cg.get_inst_coverage());

      
    svr = uvm_report_server::get_server();
 
    //se numara cate erori si cate atentionari (WARNINGs) au fost pe parcursul testului; daca a existat macar una, inseamna ca testul a picat, si trebuie reparat
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
    
    //se da directiva ca testul sa se incheie
        $finish();
  	endfunction 

endclass : test_base

task test_base::apb_write(bit[2:0] paddr, bit[7:0] pdata);

  apb_f_seq.pwrite = 1;
  apb_f_seq.paddr = paddr;
  apb_f_seq.pdata = pdata;
  apb_f_seq.start(mediu_de_verificare.agent_apb_din_mediu.sequencer_agent_apb_inst0);

endtask : apb_write

`endif