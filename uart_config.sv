`ifndef __uart_config
`define __uart_config

class uart_config extends uvm_object;

  `uvm_object_utils(uart_config)

  int data_size = 8;
  int parity_inctive = 0;
  int parity_type = 0;
  int stop_bits_number = 1;

  function new(string name = "uart_config");
    super.new(name);
  endfunction

  function void decode_uart_config(logic[7:0] reg_uart_config);
      data_size         = reg_uart_config[1:0] + 5;
      parity_inctive    = reg_uart_config[2];
      parity_type       = reg_uart_config[3];
      stop_bits_number  = reg_uart_config[4] + 1;
   endfunction

endclass : uart_config

`endif
