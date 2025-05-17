`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __secventa_apb_fixa
`define __secventa_apb_fixa

//se declara o clasa care genereaza o secventa de date
class secventa_apb_fixa extends uvm_sequence #(tranzactie_apb);
  
  //noul tip de data (secventa) se adauga la baza de date UVM
  `uvm_object_utils(secventa_apb_fixa)
  
  //se declara dimensiunea sirului
  rand bit[2:0] paddr;
  rand bit pwrite;
  rand bit[7:0] pdata;
  rand bit[5:0] delay;
  
  function new(string name="secventa_apb_fixa");
    super.new(name);
  endfunction
    
  virtual task body();
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_apb::type_id::create("req");
      
      //se incepe crearea tranzactiei
      `uvm_create(req)
      //se dau valori 
      req.paddr = this.paddr;
      req.pwrite = this.pwrite;
      req.pdata = this.pdata;
      `uvm_send(req)
      `ifdef DEBUG
      `uvm_info("SECVENTA_APB", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei();
      `endif;
  endtask

endclass : secventa_apb_fixa

`endif