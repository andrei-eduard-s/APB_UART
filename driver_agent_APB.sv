`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __apb_driver
`define __apb_driver

//driverul va prelua date de tip "tranzactie", pe care le va trimite DUT-ului, conform protocolul de comunicatie de pe interfata
class driver_agent_apb extends uvm_driver #(tranzactie_apb);
  
  //driverul se adauga in baza de date UVM
  `uvm_component_utils (driver_agent_apb)
  
  //este declarata interfata pe care driverul va trimite datele
  virtual apb_interface_dut interfata_driverului_pentru_apb;
  
  //constructorul clasei
  function new(string name = "driver_agent_apb", uvm_component parent = null);
    //este apelat constructorul clasei parinte
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    //este apelata mai intai functia build_phase din clasa parinte
    super.build_phase(phase);
    if (!uvm_config_db#(virtual apb_interface_dut)::get(this, "", "apb_interface_dut", interfata_driverului_pentru_apb))begin
      `uvm_fatal("DRIVER_AGENT_APB", "Nu s-a putut accesa interfata_apbului")
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      `uvm_info("DRIVER_AGENT_APB", $sformatf("Se asteapta o tranzactie de la sequencer"), UVM_LOW)
      seq_item_port.get_next_item(req);
      `uvm_info("DRIVER_AGENT_APB", $sformatf("S-a primit o tranzactie de la sequencer"), UVM_LOW)
      trimiterea_tranzactiei(req);
      `uvm_info("DRIVER_AGENT_APB", $sformatf("Tranzactia a fost transmisa pe interfata"), UVM_LOW)
      seq_item_port.item_done();
    end
  endtask
  
  task trimiterea_tranzactiei(tranzactie_apb informatia_de_transmis);
    $timeformat(-9, 2, " ns", 20);//cand se va afisa in consola timpul, folosind directiva %t timpul va fi afisat in nanosecunde (-9), cu 2 zecimale, iar dupa valoare se va afisa abrevierea " ns"
    
    repeat(informatia_de_transmis.delay)@(posedge interfata_driverului_pentru_apb.pclk);
    interfata_driverului_pentru_apb.psel    = 'b1;
    interfata_driverului_pentru_apb.penable = 'b0;
    interfata_driverului_pentru_apb.paddr   = informatia_de_transmis.paddr  ;
    interfata_driverului_pentru_apb.pwrite  = informatia_de_transmis.pwrite;

    if(interfata_driverului_pentru_apb.pwrite)
      interfata_driverului_pentru_apb.pwdata = informatia_de_transmis.pdata;

    @(posedge interfata_driverului_pentru_apb.pclk); //transmiterea datelor se sincronizeaza cu ceasul de sistem
    
    interfata_driverului_pentru_apb.penable = 'b1;
 
	  @(posedge interfata_driverului_pentru_apb.pclk);

    interfata_driverului_pentru_apb.psel    = 'b0;
    interfata_driverului_pentru_apb.penable = 'b0;
    interfata_driverului_pentru_apb.pwrite  = 'bx;
    interfata_driverului_pentru_apb.pwdata  = 8'bx;
    interfata_driverului_pentru_apb.prdata  = 8'bx;
    
    `ifdef DEBUG
    $display("DRIVER_AGENT_APB, dupa transmisie; [T=%0t]", $realtime);
    `endif;
  endtask
  
endclass
`endif