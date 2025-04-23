`ifndef __uart_item
`define __uart_item

class uart_item extends uvm_sequence_item;

  string name;

  rand bit [7:0] data;
  rand bit       parity;
  rand int       delay;

  constraint default_delay {
    delay >= 0;
    delay < 20;
  }

  `uvm_object_utils_begin(uart_item)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_int(parity, UVM_DEFAULT)
    `uvm_field_int(delay, UVM_DEFAULT)
  `uvm_object_utils_end


  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei
  function new(string name = "uart_item");
    super.new(name);
  endfunction

  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    `uvm_info("UART_ITEM", $sformatf("Valoarea datei: %0h. Exista paritate: %0b. Delayul este: %0d", data, parity,
             delay), UVM_NONE);
  endfunction

  function uart_item copy();
    copy = new();
    copy.data = this.data;
    copy.parity = this.parity;
    copy.delay = this.delay;
    return copy;
  endfunction : copy

endclass : uart_item

`endif
