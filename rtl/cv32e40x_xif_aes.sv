module cv32e40x_xif_aes import cv32e40x_pkg::*;
#(
  parameter int          X_NUM_RS        =  2,  // Number of register file read ports that can be used by the eXtension interface
  parameter int          X_ID_WIDTH      =  4,  // Width of ID field.
  parameter int          X_MEM_WIDTH     =  32, // Memory access width for loads/stores via the eXtension interface
  parameter int          X_RFR_WIDTH     =  32, // Register file read access width for the eXtension interface
  parameter int          X_RFW_WIDTH     =  32, // Register file write access width for the eXtension interface
  parameter logic [31:0] X_MISA          =  '0, // MISA extensions implemented on the eXtension interface
  parameter logic [ 1:0] X_ECS_XS        =  '0  // Default value for mstatus.XS
)
(
  input  logic          clk,
  input  logic          rst_n,

  // eXtension interface
  if_xif.coproc_compressed  xif_compressed_if, // Compressed interface 
  if_xif.coproc_issue       xif_issue,         // Issue interface
  if_xif.coproc_commit      xif_commit,        // Commit Interface
  if_xif.coproc_mem         xif_mem,           // Memory interface 
  if_xif.coproc_mem_result  xif_mem_result,    // Memory result interface
  if_xif.coproc_result      xif_result         // Result interface
);


logic valid, ready;
logic encrypt_middle, encrypt, decrypt, decrypt_middle;
logic [31:0] rs1, rs2, rd;
logic [1:0] byte_select;



riscv_crypto_fu_saes32 
#(
  .SAES_DEC_EN ( 1 )                 // Enable saes32 decrypt instructions.
)
aes_i
(

  .valid (valid)             , // Are the inputs valid?
  .rs1   (rs1)             , //[31:0] //! (modified) Key   
  .rs2   (rs2)             , //[31:0]//! Cipher 
  .bs    (byte_select)             , //[1:0]// Byte select immediate

  .op_saes32_encs  (encrypt) , // Encrypt SubBytes
  .op_saes32_encsm (encrypt_middle) , // Encrypt SubBytes + MixColumn
  .op_saes32_decs  (decrypt) , // Decrypt SubBytes
  .op_saes32_decsm (decrypt_middle) , // Decrypt SubBytes + MixColumn

  .rd    (rd)             , //[31:0]// output destination register value.
  .ready (ready)            // Compute finished?

);





endmodule  // cv32e40x_xif_aes