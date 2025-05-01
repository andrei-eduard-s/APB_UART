`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __input_apb_sequence
`define __input_apb_sequence

//se declara o clasa care genereaza o secventa de date
class secventa_apb extends uvm_sequence #(tranzactie_apb);
  
  //noul tip de data (secventa) se adauga la baza de date UVM
  `uvm_object_utils(secventa_apb)
  
  //se declara dimensiunea sirului
  rand int numarul_de_tranzactii;
  
  //se constrange dimensiunea sirului de tranzactii intr-un interval ales de noi
  constraint marimea_sirului_c{
    //constrangerile declarate cu cuvantul cheie "soft" se pot suprascrie ulterior
    soft numarul_de_tranzactii inside {[10:10+5]};
  }
  
  function new(string name="secventa_apb");
    super.new(name);
  endfunction
    
  function void post_randomize();
    $display("SECVENTA_apb: Marimea sirului de tranzactii=%0d", numarul_de_tranzactii);
   endfunction
  
  virtual task body();
    
    //`ifdef DEBUG
    //	$display("phase_shift= ", phase_shift);
    //`endif;
    `uvm_info("SECVENTA_APB", $sformatf("A inceput secventa cu dimensiunea de %-2d elemente", numarul_de_tranzactii), UVM_NONE)
    
    for (int i=0; i< numarul_de_tranzactii; i++) begin
      
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_apb::type_id::create("req");
      
      //se incepe crearea tranzactiei
      start_item(req);
      //se genereaza random valori in intervalele de interes pt fiecare apb 
      assert (req.randomize() with {paddr   inside {[0:7]};
                                    pdata  inside {[0:7]}; 
                                    pwrite inside {[0:1]}; 
                                    delay  inside {[0:5]}; });
      `ifdef DEBUG
      `uvm_info("SECVENTA_APB", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei();
      `endif;
      
      //s-a terminat crearea tranzactiei; aceasta poate pleca catre sequencer
      finish_item(req);
    end
    `uvm_info("SECVENTA_APB", $sformatf("S-au generat toate cele %0d tranzactii", numarul_de_tranzactii), UVM_LOW)
  endtask
endclass
`endif

class secventa_write extends uvm_sequence #(tranzactie_apb);
   `uvm_object_utils(secventa_write)
   function new(string name="secventa_write");
    super.new(name);
  endfunction 
  function void post_randomize();
  endfunction

  virtual task body();
    for (int i=0; i< 7; i++) begin
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_apb::type_id::create("req");
      
      //se incepe crearea tranzactiei
      start_item(req);
      //se genereaza random valori in intervalele de interes pt fiecare apb 
      assert (req.randomize() with {paddr inside {[0:4]};
                                    pdata  inside {[0:100]}; 
                                    pwrite == 1; 
                                    delay  inside {[0:5]}; });
      `ifdef DEBUG
      `uvm_info("SECVENTA_APB", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei();
      `endif;
      //s-a terminat crearea tranzactiei; aceasta poate pleca catre sequencer
      finish_item(req);
    end
    `uvm_info("SECVENTA_APB", $sformatf("S-au generat toate cele %0d tranzactii", numarul_de_tranzactii), UVM_LOW)
  endtask

class secventa_read extends uvm_sequence #(tranzactie_apb);
   `uvm_object_utils(secventa_read)
   function new(string name="secventa_read");
    super.new(name);
  endfunction 
  function void post_randomize();
  endfunction

  virtual task body();
    for (int i=0; i< 7; i++) begin
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_apb::type_id::create("req");
      
      //se incepe crearea tranzactiei
      start_item(req);
      //se genereaza random valori in intervalele de interes pt fiecare apb 
      assert (req.randomize() with {paddr inside {[0:4]};                                  
                                    pwrite == 0; 
                                    delay  inside {[0:5]};/*????*/ });
      `ifdef DEBUG
      `uvm_info("SECVENTA_APB", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei();
      `endif;
      //s-a terminat crearea tranzactiei; aceasta poate pleca catre sequencer
      finish_item(req);
    end
    `uvm_info("SECVENTA_APB", $sformatf("S-au generat toate cele %0d tranzactii", numarul_de_tranzactii), UVM_LOW)
  endtask
endclass