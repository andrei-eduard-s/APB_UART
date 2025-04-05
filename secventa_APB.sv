
`include "uvm_macros.svh"
import uvm_pkg::*;

//se declara o clasa care genereaza o secventa de date
class secventa_APB extends uvm_sequence #(tranzactie_APB);

//noul tip de data (secventa) se adauga la baza de date UVM
`uvm_object_utils(secventa_APB)

//se declara dimensiunea sirului
rand int numarul_de_tranzactii;

//se constrange dimensiunea sirului de tranzactii intr-un interval ales de noi
 constraint marimea_sirului_c{
 //constrangerile declarate cu cuvantul cheie "soft" se pot suprascrie ulterior
    soft numarul_de_tranzactii inside {[10:10+5]};
}

function new(string name="secventa_APB");
    super.new(name);
endfunction

function void post_randomize();
    $display("SECVENTA_apb: Marimea sirului de tranzactii=%0d", numarul_de_tranzactii);
endfunction

virtual task body();

`uvm_info("SECVENTA_APB", $sformatf("A inceput secventa cu dimensiunea de %-2d elemente", numarul_de_tranzactii), UVM_NONE)

for (int i=0; i< numarul_de_tranzactii; i++) begin
      
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_APB::type_id::create("req");
      
      //se incepe crearea tranzactiei
      start_item(req);
      //se genereaza random valori in intervalele de interes pt fiecare apb 
      assert (req.randomize() with {paddr inside {[0:3]}; 
                                    pdata inside {[0:7]}; 
                                    pwrite inside {[0:1]}; }); 

      `ifdef DEBUG
      `uvm_info("SECVENTA_apb", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei();
      `endif;
      
      //s-a terminat crearea tranzactiei; aceasta poate pleca catre sequencer
      finish_item(req);    
    end

    `uvm_info("SECVENTA_apb", $sformatf("S-au generat toate cele %0d tranzactii", numarul_de_tranzactii), UVM_LOW)
  endtask
endclass