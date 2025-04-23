`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef __irq_transaction
`define __irq_transaction

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_irq extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_irq)
  
   bit  [2:0]    irq; //output, deci nu e rand
  
  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "element_secventaa");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);  
    irq  = 0;
  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display("Valoarea IRQ: %b", irq);
  endfunction
  
  function tranzactie_irq copy();
	copy = new();
  copy.irq = this.irq;
	return copy;
  endfunction

endclass
`endif