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
    // TODO test that the onehot encoding is correct!
    
    sequence offload_instruction;
      monitor_issue.issue_req.instr[6:0] == AES32 && monitor_issue.issue_valid && monitor_issue.issue_ready;
    endsequence


    sequence issue_response_accept;
        monitor_issue.issue_resp.accept         && // AES accepts instruction
        monitor_issue.issue_resp.writeback      && // AES will perform a writeback to rd
        monitor_issue.issue_resp.dualwrite == 0 && // No write to rd and rd+1
        monitor_issue.issue_resp.dualread  == 0 && // No read from rsn and rsn+1
        monitor_issue.issue_resp.loadstore == 0 && // FU will not perform a load/store operation
        monitor_issue.issue_resp.ecswrite  == 0 && // Coprocessor will not write back to status registers
        monitor_issue.issue_resp.exc       == 0;   // No synchronous exception (cause i dont know what it is)
    endsequence

    sequence issue_response_not_accept;
        monitor_issue.issue_resp.accept    == 0 && // AES accepts instruction
        monitor_issue.issue_resp.writeback == 0 && // AES will perform a writeback to rd
        monitor_issue.issue_resp.dualwrite == 0 && // No write to rd and rd+1
        monitor_issue.issue_resp.dualread  == 0 && // No read from rsn and rsn+1
        monitor_issue.issue_resp.loadstore == 0 && // FU will not perform a load/store operation
        monitor_issue.issue_resp.ecswrite  == 0 && // Coprocessor will not write back to status registers
        monitor_issue.issue_resp.exc       == 0;   // No synchronous exception (cause i dont know what it is)
    endsequence


    // XIF issue interface
    assert property (@(posedge clk) disable iff (!rst_n)
                    (offload_instruction) |-> issue_response_accept )
        else `uvm_error("XIF", "ERROR in XIF issue response for accepted instruction");

    assert property (@(posedge clk) disable iff (!rst_n)
                    (monitor_issue.issue_req.instr[6:0] != AES32 &&
                     monitor_issue.issue_valid &&
                     monitor_issue.issue_ready) |-> issue_response_not_accept )
        else `uvm_error("XIF", "ERROR in XIF issue response for not accepted instruction");

    // Check that id of accepted instruction was output at some point
    property result_id_o;
        logic [X_ID_WIDTH-1:0] id ;
        
        (offload_instruction,
        id = monitor_issue.issue_req.id)
        ##[2:$] monitor_result.result_valid 
        |->
        monitor_result.result.id == id;
    endproperty

    // assert property (@(posedge clk) disable iff (!rst_n) result_id_o)
    //     else `uvm_error("XIF", "ERROR: accepted id not output")




    // XIF commit interface
        //Check if the id of result has been killed
    property killed_id;
        logic [X_ID_WIDTH-1:0] id;
        (monitor_commit.commit_valid && 
            monitor_commit.commit.commit_kill &&
            monitor_commit.commit.id ==  instruction_id , 
            id = monitor_commit.commit.id)
        |-> 
        ##[0:$] monitor_result.result.id != id; //Optimize this assertion (Many of these will slow verification down by a lot)
    endproperty

    assert property (@(posedge clk) disable iff (!rst_n) killed_id)
        else `uvm_error("XIF", "Result ID was killed by commit interface")


    property commit_valid_id_after_accept;
        logic [X_ID_WIDTH] id;
        (offload_instruction,
        id = monitor_issue.issue_req.id)
        |->
        ##[0:10] monitor_commit.commit_valid &&
        monitor_commit.commit.id == id
    endproperty

    assert property (@(posedge clk) disable iff (!rst_n) commit_valid_id_after_accept)
        else `uvm_error("XIF", "Commit valid or commit id was not input after accepted instruction")

    // Accepted instruction that is commited, should be output
    property instr_accept_to_result;
    logic [X_ID_WIDTH] id;
        (offload_instruction,
        id = monitor_issue.issue_req.id) ##[0:$] 
        monitor_commit.commit_valid &&
         monitor_commit.commit.commit_kill  &&
         monitor_commit.commit.id == id
         |-> ##[0:5]
         monitor_result.result.id == id &&
         monitor_result.result_valid &&
         monitor_result.result_ready;   
    endproperty

    assert property(@(posedge clk) disable iff (!rst_n) instr_accept_to_result)
        else `uvm_error("XIF", "Result never received")

    //Check that instruction is not output before commit has verified instruction
    property commited_id;
        logic [X_ID_WIDTH-1:0] id;
        (monitor_commit.commit_valid      &&
            monitor_commit.commit.commit_kill  == 0,
            id = monitor_commit.commit.id)
        |->
        ##[0:$] monitor_result.result.id == id;
    endproperty

    assert property(@(posedge clk) disable iff (!rst_n) commited_id)    
        else `uvm_error("XIF", "Result never output a commited instruction")


    // XIF result interface
    // assert property (@(posedge clk) disable iff (!rst_n)
    //                 monitor_result.result_valid
    //                     )
    
    
    






    // OLD 
    // assert property (@(posedge clk) disable iff (!rst_n)
    //                 (monitor_issue.issue_valid))
    //         `uvm_warning("XIF", $sformatf("XIF offload SUCCESS! instruction opcode = %0h", monitor_issue.issue_req.instr[6:0]))
    //     else `uvm_warning("XIF", $sformatf("XIF offload failed: instruction opcode = %0h", monitor_issue.issue_req.instr[6:0]));


    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((offload_instruction) 
    //                     |-> monitor_issue.issue_resp.accept == 1 && monitor_issue.issue_resp.writeback == 1))
    //         `uvm_warning("AES", "Op code correct, Offload success")
    //     else `uvm_error("AES", "Didnt accept correct opcode??")

    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((offload_instruction) 
    //                     |=> valid_aes_input))
    //         `uvm_warning("AES", "Offloaded instruction enables FU")
    //     else `uvm_error("AES", "offloaded instruction not valid on FU???")

    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((offload_instruction) 
    //                     |=> ready_aes_output && valid_aes_result))
    //         `uvm_warning("AES", "FU finished, returned valid")
    //     else `uvm_error("AES", "FU valid output fail")

    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((offload_instruction) 
    //                     |=> monitor_result.result_valid))
    //         `uvm_warning("XIF", "Result is valid")
    //     else `uvm_error("XIF", "Result is not valid after being accepted")
    
    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((offload_instruction) 
    //                     |=> monitor_result.result.id == $past(monitor_issue.issue_req.id, 1)))
    //         `uvm_warning("XIF", "Output id is same as input id")
    //     else `uvm_error("AES", "Output id is NOT same as input id")

    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((monitor_commit.commit_valid) |-> monitor_commit.commit.commit_kill ))
    //         `uvm_warning("AES", "Commit kill is activated")
    //     else `uvm_warning("AES", "Commit is valid but not kill")
    
    // assert property (@(posedge clk) disable iff (!rst_n)
    //                  ((monitor_result.result_valid) |->  monitor_result.result_ready ))
    //         `uvm_warning("XIF", "XIF ready and valid became high")
    //     else `uvm_warning("AES", "XIF ready and valid was never high at the same time")

endmodule // cv32e40x_aes_sva
