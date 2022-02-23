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
   if_xif.monitor_issue monitor_issue,
   if_xif.monitor_commit monitor_commit,
   if_xif.monitor_result monitor_result,

    // Internal signals
   input logic valid_aes_input, 
   input logic valid_aes_result,
   input logic ready_aes_output,
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
    sequence offload_instruction;
      monitor_issue.issue_req.instr[6:0] == AES32 && monitor_issue.issue_valid;
    endsequence


    assert property (@(posedge clk) disable iff (!rst_n)
                    (monitor_issue.issue_valid))
            `uvm_warning("XIF", $sformatf("XIF offload SUCCESS! instruction opcode = %0h", monitor_issue.issue_req.instr[6:0]))
        else `uvm_warning("XIF", $sformatf("XIF offload failed: instruction opcode = %0h", monitor_issue.issue_req.instr[6:0]));


    assert property (@(posedge clk) disable iff (!rst_n)
                     ((offload_instruction) 
                        |-> monitor_issue.issue_resp.accept == 1 && monitor_issue.issue_resp.writeback == 1))
            `uvm_warning("AES", "Op code correct, Offload success")
        else `uvm_error("AES", "Didnt accept correct opcode??")

    assert property (@(posedge clk) disable iff (!rst_n)
                     ((offload_instruction) 
                        |=> valid_aes_input))
            `uvm_warning("AES", "Offloaded instruction enables FU")
        else `uvm_error("AES", "offloaded instruction not valid on FU???")

    assert property (@(posedge clk) disable iff (!rst_n)
                     ((offload_instruction) 
                        |=> ready_aes_output && valid_aes_result))
            `uvm_warning("AES", "FU finished, returned valid")
        else `uvm_error("AES", "FU valid output fail")

    assert property (@(posedge clk) disable iff (!rst_n)
                     ((offload_instruction) 
                        |=> monitor_result.result_valid))
            `uvm_warning("XIF", "Result is valid")
        else `uvm_error("XIF", "Result is not valid after being accepted")
    
    assert property (@(posedge clk) disable iff (!rst_n)
                     ((offload_instruction) 
                        |=> monitor_result.result.id == $past(monitor_issue.issue_req.id, 1)))
            `uvm_warning("XIF", "Output id is same as input id")
        else `uvm_error("AES", "Output id is NOT same as input id")

    assert property (@(posedge clk) disable iff (!rst_n)
                     ((monitor_commit.commit_valid) |-> monitor_commit.commit.commit_kill ))
            `uvm_warning("AES", "Commit kill is activated")
        else `uvm_warning("AES", "Commit is valid but not kill")
    
    assert property (@(posedge clk) disable iff (!rst_n)
                     ((monitor_result.result_valid) |->  monitor_result.result_ready ))
            `uvm_warning("XIF", "XIF ready and valid became high")
        else `uvm_warning("AES", "XIF ready and valid was never high at the same time")

endmodule // cv32e40x_aes_sva
