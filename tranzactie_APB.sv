`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __apb_transaction
`define __apb_transaction

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_apb extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_apb)
  
  rand bit[2:0] paddr;
  rand bit[7:0] pdata;

  rand bit pwrite;
  rand bit [5:0] delay; 

  
  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "element_secventaa");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);  
  	paddr   = 0;
    pdata  = 0;
    pwrite = 0;
    delay  = 1;
  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display("Valoarea adresei: %0h, Valoarea datelor: %0h, Valoarea write: %0h, Valoarea delay: %0h", paddr, pdata, pwrite, delay);
  endfunction
  
  function tranzactie_apb copy();
	copy = new();
	copy.paddr  = this.paddr;
  copy.paddr  = this.paddr;
	copy.pdata  = this.pdata;
	copy.pwrite = this.pwrite;
  copy.delay  = this.delay;
	return copy;
  endfunction

endclass
`endif