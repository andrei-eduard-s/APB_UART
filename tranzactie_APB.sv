`ifndef __APB_transaction
`define __APB_transaction

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_APB extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_APB)
  
  rand bit[2:0] paddr;
  rand bit[3:0] pwdata;

  rand bit pwrite;
  bit perror;
  unsigned delay;

  
  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "element_APB");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);  
    paddr  = 2;
  	pwdata = 5;
  	pwrite = 1;
    perror = false;
    delay = 3;
  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display("Valoarea adresei: %0h, Valoarea datelor: %0h, Valoarea write: %0h, Valoarea error: %0h, Valoarea delay: %0h", paddr, pwdata, pwrite, perror, delay);
  endfunction
  
  function tranzactie_APB copy();
	copy = new();
	copy.paddr  = this.paddr;
	copy.pwdata = this.pwdata;
	copy.pwrite = this.pwrite;
  copy.perror = this.perror;
  copy.delay  = this.delay;
	return copy;
  endfunction

endclass
`endif