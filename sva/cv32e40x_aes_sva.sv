////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Author:         Aleksander Waage - alekswaa@stud.ntnu.no                   //
//                                                                            //
// Description:    RTL assertions for the aes module                          //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_aes_sva
  import uvm_pkg::*;
  import cv32e40x_pkg::*;
  #(
    parameter int          X_NUM_RS        =  2,  // Number of register file read ports that can be used by the eXtension interface
    parameter int          X_ID_WIDTH      =  4,  // Width of ID field.
    parameter int          X_MEM_WIDTH     =  32, // Memory access width for loads/stores via the eXtension interface
    parameter int          X_RFR_WIDTH     =  32, // Register file read access width for the eXtension interface
    parameter int          X_RFW_WIDTH     =  32, // Register file write access width for the eXtension interface
    parameter logic [31:0] X_MISA          =  '0, // MISA extensions implemented on the eXtension interface
    parameter logic [ 1:0] X_ECS_XS        =  '0  
  )
  (// Module boundary signals
   input logic        clk,
   input logic        rst_n,

  // eXtension interface
   if_xif.coproc_issue xif_issue,
   if_xif.coproc_commit xif_commit,
   if_xif.coproc_result xif_result,

    // Internal signals
   input logic valid_aes_input, 
   input logic valid_aes_result,
   input logic issue_ready_aes,
   input logic is_instruction_not_kill,
   input logic encrypt_i, 
   input logic encrypt_middle_i, 
   input logic decrypt_i, 
   input logic decrypt_middle_i,
   input logic [1:0] byte_select_i,
   input logic [X_RFR_WIDTH-1:0] rs1_i,
   input logic [X_RFR_WIDTH-1:0] rs2_i, 
   input logic [X_RFR_WIDTH-1:0] result_aes_o, 
   input logic [X_RFR_WIDTH-1:0] rd,
   input logic [31:0] instruction,
   input logic [X_ID_WIDTH-1:0] instruction_id,
   input logic [4:0] rd_register_adr
   );

  ////////////////////////////////////////
  ////  Assertions on module boundary ////
  ////////////////////////////////////////

    // logic correct_AES_opcode; 
    // assign correct_AES_opcode = instruction[6:0] == AES32 ? 1 : 0;
    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((instruction[6:0] == AES32) &&  issue_ready_aes && xif_issue.issue_req.valid|-> xif_issue.issue_resp.accept == 1 && xif_issue.issue_resp.writeback == 1))
    //         `uvm_error("AES", "XIF AES offload successfull")
    //     else `uvm_error("AES", "XIF AES offload failed")

//   // Check result for MUL
//   logic [31:0] mul_result;
//   assign mul_result = $signed(op_a_i) * $signed(op_b_i);
  // a_mul_result : // check multiplication result for MUL
  //   assert property (@(posedge clk) disable iff (!rst_n)
  //                    (valid_i && (operator_i == MUL_M32)) |-> (result_o == mul_result))
  //     else `uvm_error("mult", "MUL result check failed")
//   a_mul_valid : // check that MUL result is immediately qualified by valid_o
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (valid_i && (operator_i == MUL_M32)) |-> valid_o)
//       else `uvm_error("mult", "MUL result wasn't immediately valid")


//   // Check result for all MULH flavors 
//   logic               mulh_result_valid;
//   assign mulh_result_valid = ((operator_i == MUL_H) && valid_i) && valid_o;

//   logic [31:0] mulh_result;
//   assign mulh_result = ($signed({{32{op_a_i[31]}}, op_a_i}) * $signed({{32{op_b_i[31]}}, op_b_i})) >>> 32;
//   a_mulh_result : // check multiplication result for MULH
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_result_valid && (signed_mode_i == 2'b11)) |->
//                      (result_o == mulh_result))
//       else `uvm_error("mult", "MULH result check failed")

//   logic [31:0] mulhsu_result;
//   assign mulhsu_result = ($signed({{32{op_a_i[31]}}, op_a_i}) * {32'b0, op_b_i}) >> 32;
//   a_mulhsu_result : // check multiplication result for MULHSU
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_result_valid && (signed_mode_i == 2'b01)) |->
//                      (result_o == mulhsu_result))
//       else `uvm_error("mult", "MULHSU result check failed")

//   logic [31:0] mulhu_result;
//   assign mulhu_result = ({32'b0, op_a_i} * {32'b0, op_b_i}) >> 32;
//   a_mulhu_result : // check multiplication result for MULHU
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_result_valid && (signed_mode_i == 2'b00)) |->
//                      (result_o == mulhu_result))
//       else `uvm_error("mult", "MULHU result check failed")


//   // Check signal stability
//   sequence s_insistent_valid;
//     @(posedge clk)
//     (valid_i && !ready_o) ##1 valid_i;
//   endsequence

//   a_operator_constant_when_mulh_active:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      s_insistent_valid |-> $stable(operator_i))
//       else `uvm_error("mult", "Operator changed when MULH active")

//   a_sign_constant_when_mulh_active:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      s_insistent_valid |-> $stable(signed_mode_i))
//       else `uvm_error("mult", "Sign changed when MULH active")

//   a_operand_a_constant_when_mulh_active:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      s_insistent_valid |-> $stable(op_a_i))
//       else `uvm_error("mult", "Operand A changed when MULH active")

//   a_operand_b_constant_when_mulh_active:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      s_insistent_valid |-> $stable(op_b_i))
//       else `uvm_error("mult", "Operand B changed when MULH active")

//   a_check_result_constant: // Check that the result is kept stable until receiver is ready
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (valid_o && !ready_i) ##1 valid_o |-> $stable(result_o))
//       else `uvm_error("mult", "Completed result changed while receiving end was not ready")


//   // Check handshake properties

//   a_outputs_are_input_qualified:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      valid_o |-> valid_i)
//       else `uvm_error("mult", "Outputs valid while inputs where unknown")

//   a_can_receive_expediently:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (valid_o && ready_i) |-> ready_o)
//       else `uvm_error("mult", "Outputs where consumed but didn't get ready for new inputs")


//   //////////////////////////////
//   ////  Internal assertions ////
//   //////////////////////////////

//   // Check initial value of accumulate register
//   a_check_acc_init_zero:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_state == MUL_ALBL) |-> (mulh_acc == '0))
//       else `uvm_error("mult", "Accumulate register not 0 when starting MULH calculation")

//   // Check that accumulate register is 0 for MUL
//   a_check_acc_mul_value_zero:
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (operator_i == MUL_M32) && valid_i |-> (mulh_acc == '0))
//       else `uvm_error("mult", "Accumulate register not 0 for MUL instruction")


//   // Check result for intermediary stages of the 4-step shift-and-add algorithm

//   //Here are checks for the `int_result` of the 4 steps.
//   //There are also checks for `mulh_acc` for the 3 last steps.
//   //At the final step, `int_result + mulh_acc` represents the final `result_o`.

//   logic [33:0] shift_result_ll;
//   logic [33:0] shift_result_lh;
//   logic [33:0] shift_result_hl;
//   logic [33:0] shift_result_hh;
//   logic [33:0] shift_result_ll_shift;
//   logic [32:0] shift_result_ll_lh;
//   logic [33:0] shift_result_ll_lh_hl;
//   logic [32:0] shift_result_ll_lh_hl_shift;
//   logic unused;

//   assign shift_result_ll = $signed({{16{mulh_al[16]}}, mulh_al[15:0]}) * $signed({{16{mulh_bl[16]}}, mulh_bl[15:0]});
//   a_shift_result_ll : // Given MUL_H, first calculation is "al * bl"
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      ((mulh_state == MUL_ALBL) && valid_i && (operator_i == MUL_H)) |->
//                      (int_result == shift_result_ll))
//       else `uvm_error("mult", "MUL_H step 1/4 got wrong int_result")

//   assign shift_result_lh = $signed({{16{mulh_al[16]}}, mulh_al[15:0]}) * $signed({{16{mulh_bh[16]}}, mulh_bh[15:0]});
//   a_shift_result_lh : // Second calculation is "al * bh"
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_state == MUL_ALBH) && valid_i |->
//                      (int_result == shift_result_lh))
//       else `uvm_error("mult", "MUL_H step 2/4 got wrong int_result")

//   assign shift_result_hl = $signed({{16{mulh_ah[16]}}, mulh_ah[15:0]}) * $signed({{16{mulh_bl[16]}}, mulh_bl[15:0]});
//   a_shift_result_hl : // Third calculation is "ah * bl"
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_state == MUL_AHBL) && valid_i |->
//                      (int_result == shift_result_hl))
//       else `uvm_error("mult", "MUL_H step 3/4 got wrong int_result")

//   assign shift_result_hh = $signed({{16{mulh_ah[16]}}, mulh_ah[15:0]}) * $signed({{16{mulh_bh[16]}}, mulh_bh[15:0]});
//   a_shift_result_hh : // Fourth and final multiplication is "ah * bh"
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_state == MUL_AHBH) && valid_i |->
//                      (int_result == shift_result_hh))
//       else `uvm_error("mult", "MUL_H step 4/4 got wrong int_result")

//   assign shift_result_ll_shift = (shift_result_ll) >> 16;
//   a_shift_result_ll_shift : // In step 2, accumulate the shifted result of "al * bl"
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_state == MUL_ALBH) && valid_i |->
//                      (mulh_acc == shift_result_ll_shift))
//       else `uvm_error("mult", "MUL_H accumulated 'al x bl' wrong")

//   assign {unused, shift_result_ll_lh} = $signed(shift_result_ll_shift) + $signed(shift_result_lh);
//   a_shift_result_ll_lh : // In step 3, accumulate also result of "al * bh"
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_state == MUL_AHBL) && valid_i |->
//                      (mulh_acc == shift_result_ll_lh))
//       else `uvm_error("mult", "MUL_H accumulated 'al x bh' wrong")

//   assign shift_result_ll_lh_hl = $signed(shift_result_ll_lh) + $signed(shift_result_hl);
//   assign shift_result_ll_lh_hl_shift = $signed(shift_result_ll_lh_hl) >>> 16;
//   a_shift_result_ll_lh_hl_shift : // In step 4, accumulate also "ah * bl" and store the shifted result
//     assert property (@(posedge clk) disable iff (!rst_n)
//                      (mulh_state == MUL_AHBH) && valid_i |->
//                      (mulh_acc == shift_result_ll_lh_hl_shift))
//       else `uvm_error("mult", "MUL_H accumulated 'ah x bl' wrong")

endmodule // cv32e40x_aes_sva
