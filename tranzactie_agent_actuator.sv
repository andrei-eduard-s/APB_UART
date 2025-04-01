`ifndef __transaction
`define __transaction

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_agent_actuator extends uvm_sequence_item;

  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_agent_actuator)

  //semnalul de intrerupere observat de monitor
  rand bit [2:0] interrupt;

  //constructorul clasei; aceasta functie este apelata cand se creeaza un obiect de tip tranzactie
  function new(string name = "element_secventa");
    super.new(name);
    interrupt = 3'b000;
  endfunction

  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display("valoarea intreruperii: %03b", interrupt);
  endfunction

  //functie prin care se compara 2 tranzactii
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    //primele 4 linii pot fi considerate cod standard
    bit res;
    tranzactie_agent_actuator _obj;
    $cast(_obj, rhs);
    res = super.do_compare(_obj, comparer) && (interrupt == _obj.interrupt);
    `uvm_info(get_name(), $sformatf("in tranzactie_agent_actuator::do_compare(), rezultatul comparatiei este %0b", res), UVM_LOW)
    return res;
  endfunction

  //functie pentru copiere completa (deep copy)
  function tranzactie_agent_actuator copy();
    copy = new();
    copy.interrupt = this.interrupt;
    return copy;
  endfunction

endclass

`endif