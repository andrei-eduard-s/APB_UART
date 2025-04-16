`include "uvm_macros.svh"
import uvm_pkg::*;

class scoreboard extends uvm_scoreboard;

  `uvm_component_utils(scoreboard)

  uvm_analysis_imp_apb #(tranzactie_APB, scoreboard) port_pentru_datele_de_la_apb;
  uvm_analysis_imp_uart #(uart_item, scoreboard) port_pentru_datele_de_la_uart;
  uvm_analysis_imp_int #(tranzactie_agent_actuator, scoreboard) port_pentru_datele_de_la_int;

  uart_config p_uart_cfg;
  
  bit [7:0] tx_fifo [0:15];  // Array to mimic the 16-entry TX FIFO
  int fifo_wr_ptr;           // Write pointer for the FIFO
  int fifo_rd_ptr;           // Read pointer for the FIFO
  int fifo_count;            // Number of items in the FIFO
  
  logic [7:0] reg_data_tx; // addr 0
  logic [7:0] reg_data_rx; // addr 2
  logic [7:0] reg_status; // addr 3
  logic [7:0] reg_uart_config // addr 4

  
function new(string name = "scoreboard", uvm_component parent = null);
super.new(name, parent);
port_pentru_datele_de_la_apb = new("port_pentru_datele_de_la_apb", this);
port_pentru_datele_de_la_uart = new("port_pentru_datele_de_la_uart", this);
port_pentru_datele_de_la_int = new ("port_pentru_datele_de_la_int", this);
`uvm_info("SCOREBOARD", "scoreboard constructor called!", UVM_MEDIUM);
endfunction : new
  

  // Build phase - set up initial configurations or variables
  function void build_phase(uvm_phase phase);
  
    super.build_phase(phase);  // Call parent build_phase
	
	// Add initialization code here (e.g., variables, queues, etc.)
  if (!uvm_config_db#(uart_config)::get(this, "", "uart_cfg", p_uart_cfg))
   `uvm_fatal("NOVCFG", "Failed to get UART config from config DB")

	fifo_wr_ptr = 0; // starts at the beginning of the FIFO
	fifo_rd_ptr = 0; // (empty) also starts at the beginning
	fifo_count = 0; // No items in the FIFO at the start
	bit [7:0] rx_reg;  // Single register for RX data
	bit rx_valid;      // Flag to indicate if RX data is available
	
  endfunction : build_phase
  
  


  // Write method for APB transactions
  virtual function void write_apb(tranzactie_APB t);
    // Add code here to process APB transactions
	if (t.pwrite == 1) begin//daca avem tranzactie de scriere
		case (paddr)
		0: reg_data_tx = t.pdata;
		2: `uvm_info(get_full_name(), "REGISTRU READ_ONLY, nu se poate scrie", UVM_LOW)
		3: `uvm_info(get_full_name(), "REGISTRU READ_ONLY, nu se poate scrie", UVM_LOW)
		4: begin 
        reg_uart_config = t.pdata;
        p_uart_cfg.decode_uart_config(reg_uart_config);
    end

		default: `uvm_info(get_full_name(), "adresa incorecta", UVM_LOW)
		endcase
		end
		else
		begin//daca avem citire
		case(paddr)
		0:`uvm_info(get_full_name(), "REGISTRU WRiTE_ONLY, nu se poate Citi", UVM_LOW)
		2: assert (reg_data_rx == t.pdata) else `uvm_error("valoarea prezisa de dut: %0h, valoarea din scoreboard: %0h", t.pdata, reg_data_rx);
		3: assert (reg_status == t.pdata) else `uvm_error("valoarea prezisa de dut: %0h, valoarea din scoreboard: %0h", t.pdata, reg_status);
		4: assert (reg_uart_config == t.pdata) else `uvm_error("valoarea prezisa de dut: %0h, valoarea din scoreboard: %0h", t.pdata, reg_uart_config);
		
		end
  endfunction : write_apb



  // Write method for UART transactions
  virtual function void write_uart(uart_item t);
  bit only_data_parity = ^t.data;
    // Add code here to process UART transactions
	reg_data_rx = t.data;
	
	//daca avem paritate si daca paritatea este para
	if (reg_uart_config[2] == 1 && reg_uart_config[3] == 0)
	if (^{t.data,t.parity} == 0) 
	reg_status[3] = 0; // nu am eroare de paritate
	else begin //am eroare de paritate
	`uvm_error("valoarea de paritate este gresita: %0h pentru data: %0h", t.parity, t.data);
	reg_status[3] =1;
	end
//daca avem paritate si daca paritatea este impara
	if (reg_uart_config[2] == 1 && reg_uart_config[3] == 1)
	if (^{t.data,t.parity} == 1) 
	reg_status[3] = 0; // nu am eroare de paritate
	
	else begin //am eroare de paritate
	`uvm_error("valoarea de paritate este gresita: %0h pentru data: %0h", t.parity, t.data);
	reg_status[3] =1;
	end		
  endfunction : write_uart
  
  

  // Write method for interrupt transactions
  virtual function void write_int(tranzactie_agent_actuator t);
    // Add code here to process interrupt transactions
  endfunction : write_int
  
  

  // Run phase - main execution loop
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);  // Call parent run_phase
    // Add continuous checking or processing code here
  endtask : run_phase
  
  
endclass