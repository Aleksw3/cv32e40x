module cv32e40x_xif_aes import cv32e40x_pkg::*;
#(
  parameter int          X_ID_WIDTH      =  4,  // Width of ID field.
  parameter int          X_RFR_WIDTH     =  32, // Register file read access width for the eXtension interface
  parameter logic [ 1:0] X_ECS_XS        =  '0, // Default value for mstatus.XS
  parameter int          PROTECTED       =   0
)
(
  input  logic          clk_i,
  input  logic          rst_n,

  // eXtension interface
  if_xif.coproc_issue       xif_issue,         // Issue interface
  if_xif.coproc_commit      xif_commit,        // Commit Interface
  if_xif.coproc_result      xif_result         // Result interface
);

    logic valid_aes_input, ready_aes_output;
    logic is_instruction_accepted, accept_instruction;
    logic issue_ready_aes;
    logic encrypt_middle_i, encrypt_i, decrypt_i, decrypt_middle_i;
    logic commit_valid, commit_kill;
    logic is_commit_kill, is_commit_accept, kill_instruction, commit_instruction;
    logic save_commit;

    logic ready_input;

    logic [1:0]              byte_select_i;
    logic [X_RFR_WIDTH-1:0]  rs1_i, rs2_i, result_aes_o, rd;
    logic [X_ID_WIDTH-1:0]   instruction_id;
    logic [31:0]             instruction;
    logic [4:0]              rd_register_adr;
    logic [35:0] randombits;

    logic [7:0] shareB_rand;
    assign shareB_rand = 8'h02;

    // XIF issue interface response
    assign xif_issue.issue_resp.accept    = accept_instruction;
    assign xif_issue.issue_resp.writeback = accept_instruction;
    assign xif_issue.issue_resp.dualwrite = 0;
    assign xif_issue.issue_resp.dualread  = 0;
    assign xif_issue.issue_resp.loadstore = 0;
    assign xif_issue.issue_resp.ecswrite  = 0;
    assign xif_issue.issue_resp.exc       = 0;

    // XIF result interface
    assign xif_result.result.data    = result_aes_o;
    assign xif_result.result.rd      = rd_register_adr;
    assign xif_result.result.id      = instruction_id;
    assign xif_result.result.we      = 1'b1;
    assign xif_result.result.ecswe   = 1'b0;
    assign xif_result.result.ecsdata =   '0;
    assign xif_result.result.exc     = 1'b0;
    assign xif_result.result.exccode =   '0;



    assign valid_aes_input = is_instruction_accepted;
    assign byte_select_i   = instruction[31:30];
    assign rd_register_adr = instruction[11:7];

    // Accept instruction
    assign issue_ready_aes = !is_instruction_accepted || (kill_instruction || (xif_result.result_valid && xif_result.result_ready));
    assign xif_issue.issue_ready = issue_ready_aes;

    always_comb
    begin : ACCEPT_OFFLOADED_INSTRUCTION
        accept_instruction = 0;

        if(xif_issue.issue_req.instr[6:0] == AES32 &&
           xif_issue.issue_valid &&
           issue_ready_aes) 
        begin
            accept_instruction = 1;
        end
    end

    always_comb
    begin : ONEHOT_AES_INSTR_TYPE
        decrypt_i        = 0;
        decrypt_middle_i = 0;
        encrypt_i        = 0;
        encrypt_middle_i = 0;
        if(valid_aes_input) begin
            unique case(instruction[29:25])
                AES32DSI:  decrypt_i        = 1;
                AES32DSMI: decrypt_middle_i = 1;
                AES32ESI:  encrypt_i        = 1;
                AES32ESMI: encrypt_middle_i = 1;
            endcase
        end
    end

    // Pass values from XIF to the AES FU
    always_ff @(posedge clk_i, negedge rst_n)
        begin : ACCEPT_INS_SAVE_VALS
        if (rst_n == 1'b0)
        begin
            rs1_i            = '0;
            rs2_i            = '0;
            instruction_id   = '0;
            instruction      =  0;
            is_instruction_accepted = 0;
        end else 
        begin
            if (!(valid_aes_input) || (kill_instruction || (xif_result.result_valid && xif_result.result_ready)))
                is_instruction_accepted = accept_instruction;

            if(accept_instruction) 
            begin
                instruction = xif_issue.issue_req.instr;
                instruction_id = xif_issue.issue_req.id;

                //TODO: how to handle if one of rs are invalid? Should in theory (assumably) not happen
                if(xif_issue.issue_req.rs_valid ==? 3'bxx1) begin
                    rs1_i = xif_issue.issue_req.rs[0];
                end 

                if(xif_issue.issue_req.rs_valid ==? 3'bx1x) begin
                    rs2_i = xif_issue.issue_req.rs[1];
                end 
            end
        end
    end

    always_comb 
    begin : TO_BE_KILLED_OR_NOT_TO_BE_KILLED
        kill_instruction   = 1'b0;
        commit_instruction = 1'b0;

        if (xif_commit.commit.id == instruction_id) 
        begin
            if (xif_commit.commit_valid && xif_commit.commit.commit_kill)
                kill_instruction = 1'b1;
            else if (xif_commit.commit_valid && !xif_commit.commit.commit_kill)
                commit_instruction = 1'b1;
        end
    end


    assign xif_result.result_valid = ready_aes_output && (save_commit || commit_instruction);

    always_ff @(posedge clk_i, negedge rst_n ) 
    begin : SAVE_COMMIT_WHEN_RESULT_READY_i_LOW
        if(rst_n == 1'b0)
            save_commit = 1'b0;
        else begin
            if (xif_result.result_ready)
                save_commit = 1'b0;
            else if (xif_result.result_ready == 1'b0 && save_commit == 1'b0)
                save_commit = commit_instruction;
        end
    end

generate if(PROTECTED) begin: PREOTECTED_AES
    riscv_crypto_fu_saes32_protected
    aes_prot_i
    (
        .clk(clk),
        .reset_n(reset_n),

        .valid           (valid_aes_input)  ,
        .ready_input     (ready_input)      ,
        .rs1             (rs1_i)            , 
        .rs2             (rs2_i)            , 
        .shareB_in       (shareB_rand)      ,
        .randombits      (randombits)       , 

        .bs(byte_select_i)                  ,

        .op_saes32_decs(decrypt_i)          ,
        .op_saes32_decsm(decrypt_middle_i)  ,
        .op_saes32_encs(encrypt_i)          ,
        .op_saes32_encsm(encrypt_middle_i)  ,

        .rd(result_aes_o),
        .rd_ready_o(ready_aes_output)
    );

end else begin
    riscv_crypto_fu_saes32 
    #(
        .SAES_DEC_EN ( 1 )                 // Enable saes32 decrypt instructions.
    )
    aes_i
    (
        .valid           (valid_aes_input)  ,
        .rs1             (rs1_i)            , 
        .rs2             (rs2_i)            , 
        .bs              (byte_select_i)    ,

        .op_saes32_encs  (encrypt_i)        , // Encrypt SubBytes
        .op_saes32_encsm (encrypt_middle_i) , // Encrypt SubBytes + MixColumn
        .op_saes32_decs  (decrypt_i)        , // Decrypt SubBytes
        .op_saes32_decsm (decrypt_middle_i) , // Decrypt SubBytes + MixColumn

        .rd              (result_aes_o)     , // output destination register value.
        .ready           (ready_aes_output)   // Compute finished?
    );
end endgenerate

endmodule  // cv32e40x_xif_aes