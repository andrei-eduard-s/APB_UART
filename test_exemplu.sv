`ifndef __test_exemplu
`define __test_exemplu

`include "uvm_macros.svh"
//se includ fisierele la care testul trebuie sa aiba acces
`include "mediu_verificare.sv"
`include "secventa_apb.sv"
`include "uart_sequence.sv"

class test_exemplu extends uvm_test;

  `uvm_component_utils(test_exemplu)
  
  //se declara constructorul testului
  function new(string name = "test_exemplu", uvm_component parent=null);
    super.new(name, parent);
  endfunction
  
  
  
  //se instantiaza mediul de verificare
  mediu_verificare mediu_de_verificare;
  
  //se instantiaza secventa folosita de agent_buton si agent_actuator
  secventa_apb apb_seq;
  uart_sequence uart_seq;
  
  //se instantiaza interfetele virtuale ale mediului de verificare; acestea vor fi ulterior corelate cu interfetele reale definite in fisierele interfata_intrari_dut si interfata_semafoare

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

    //se creaza mediul de verificare declarat mai sus
    mediu_de_verificare = mediu_verificare::type_id::create("mediu_de_verificare", this);
    
    //Get virtual IF handle from top_level and pass it to everything in env level
    if (!uvm_config_db#(virtual apb_interface_dut)::get(this, "", "apb_interface_dut", vif_apb_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala apb_interface_dut pentru a crea vif_apb_dut")
    if (!uvm_config_db#(virtual irq_interface_dut)::get(this, "", "irq_interface_dut", vif_irq_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala irq_interface_dut pentru a crea vif_irq_dut")
    if (!uvm_config_db#(virtual uart_interface_dut)::get(this, "", "uart_interface_dut", vif_uart_dut))
      `uvm_fatal("TEST", "Nu s-a putut obtine din baza de date UVM tipul de interfata virtuala uart_interface_dut pentru a crea vif_uart_dut")

      //interfetele virtuale sunt folosite pentru a crea conexiunile cu agentii
    // uvm_config_db#(virtual irq_interface_dut)::set(this, "mediu_de_verificare.agent_irq_din_mediu.*", "irq_interface_dut",vif_irq_dut);
    // uvm_config_db#(virtual apb_interface_dut)::set(this, "mediu_de_verificare.agent_apb_din_mediu.*", "apb_interface_dut",vif_apb_dut);
    // uvm_config_db#(virtual uart_interface_dut)::set(this, "mediu_de_verificare.agent_uart_din_mediu.*", "uart_interface_dut",vif_uart_dut);

    //Se creaza secventele de date de intrare (in cazul de fata avem doar o secventa, deoarece avem doar un agent activ), dandu-se apoi valori aleatoare campurilor declarate cu cuvantul cheie "rand" din interiorul clasei "secventa_intrari"

    apb_seq = secventa_apb::type_id::create("apb_seq");
    apb_seq.randomize();

    uart_seq = uart_sequence::type_id::create("uart_seq");
    uart_seq.randomize();
    
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    
    //se apeleaza functia run_phase din clasa parinte
    super.run_phase(phase);
    
    //se activeaza un martor ("obiectie") ca am inceput o activitate; pana cand nu se termina activitatea, simulatorul va sti ca nu trebuie sa intrerupe faza "run" din rularea testului; de aceea trebuie sa avem grija ca la sfarsitul acestei functii sa dezactivam martorul de activitate
    phase.raise_objection(this);
    
    //se aserteaza semnalele de reset din interfete
    // apply_reset();
    `uvm_info("test_exemplu", "real execution begins", UVM_NONE);
    
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
    #100//se mai asteapta 100 de unitati de timp inainte sa se dezactiveze martorul de activitate, actiune care va permite simulatorului sa incheie activitatea
	//se dezactiveaza martorul 
    phase.drop_objection(this);
  endtask : run_phase
  
  //traficul de pe interfete este resetat
  // virtual task apply_reset();
  //   vif_apb_dut.preset_n <= 0;
  //   vif_apb_dut.paddr    <= 0;
  //   vif_apb_dut.penable  <= 0;
  //   vif_apb_dut.psel     <= 0;

  //   vif_uart_dut.reset_n <= 0;
  //   vif_uart_dut.uart_tx <= 1;
  //   vif_uart_dut.uart_rx <= 1;
  //   `ifdef DEBUG
  //   $display("am asertat resetul");
  //   `endif;
  //   repeat(15) @(posedge vif_apb_dut.pclk);
  //   vif_apb_dut.preset_n <= 1;
  //   vif_uart_dut.reset_n <= 1;
  //   `ifdef DEBUG
  //   $display("%t am deasertat resetul", $time());
  //   `endif;
  // endtask
  
  //in aceasta faza, care se desfasoara dupa faza de run in care se intampla actiunea propriu-zisa in mediul de verificare, afisam valorile de coverage
  virtual function void report_phase(uvm_phase phase);
    uvm_report_server svr;
    super.report_phase(phase);
    $display("STDOUT: Valorile de coverage obtinute pentru apb sunt: %3.2f%% ",  		   mediu_de_verificare.agent_apb_din_mediu.monitor_apb_inst0.colector_coverage_apb.stari_apb_cg.get_inst_coverage());

      
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
endclass
`endif
