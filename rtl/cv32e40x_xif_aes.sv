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
  if_xif.coproc_issue       xif_issue,         // Issue interface
  if_xif.coproc_commit      xif_commit,        // Commit Interface
  if_xif.coproc_result      xif_result         // Result interface
);

    logic valid_aes_input, ready_aes_output;
    logic is_instruction_accepted, accept_instruction;
    logic issue_ready_aes;
    logic is_instruction_not_kill;
    logic encrypt_middle_i, encrypt_i, decrypt_i, decrypt_middle_i;
    logic valid_aes_result;

    logic [1:0]              byte_select_i;
    logic [X_RFR_WIDTH-1:0]  rs1_i, rs2_i, result_aes_o, rd;
    logic [X_ID_WIDTH-1:0]   instruction_id;
    logic [31:0]             instruction;
    logic [4:0]              rd_register_adr;



    // XIF issue interface response
    assign xif_issue.issue_resp.accept    = is_instruction_accepted;
    assign xif_issue.issue_resp.writeback = is_instruction_accepted;
    assign xif_issue.issue_resp.dualwrite = 0;
    assign xif_issue.issue_resp.loadstore = 0;
    assign xif_issue.issue_resp.ecswrite  = 0;
    assign xif_issue.issue_resp.exc       = 0; //? what is a synchronous exception


    // XIF result interface response
    assign xif_result.result_valid = valid_aes_result;
    assign xif_result.result.id    = instruction_id;
    assign xif_result.result.data  = rd;
    assign xif_result.result.rd    = rd_register_adr;
    assign xif_result.result.we    = 1;


    assign valid_aes_input         = is_instruction_accepted;
    assign byte_select_i   = instruction[31:30];
    assign rd_register_adr = instruction[11:7];

    assign issue_ready_aes = !valid_aes_result || (valid_aes_result && xif_result.ready);
    assign xif_issue.ready = issue_ready_aes;

    always_comb
    begin : ACCEPT_OFFLOADED_INSTRUCTION
        accept_instruction = 0;

        if(xif_issue.issue_req.instr[6:0] == AES32 &&
           xif_issue.issue_req.valid &&
           issue_ready_aes) 
        begin
            accept_instruction = 1;
        end
    end

    //TODO rename signals
    always_comb
    begin : ONEHOT_AES_ROUND_SELECT
        decrypt_i        = 0;
        decrypt_middle_i = 0;
        encrypt_i        = 0;
        encrypt_middle_i = 0;
        unique case(instruction[29:25])
            AES32DSI:  decrypt_i        = 1;
            AES32DSMI: decrypt_middle_i = 1;
            AES32ESI:  encrypt_i        = 1;
            AES32ESMI: encrypt_middle_i = 1;
        endcase
    end

    // Pass values from XIF to the AES FU
    always_ff @(posedge clk, negedge rst_n)
        begin : ID_FU_AES
        if (rst_n == 1'b0)
        begin
            rs1_i            = '0;
            rs2_i            = '0;
            instruction_id   = '0;
            instruction      =  0;
            is_instruction_accepted = 0;
        end else 
        begin
            rs1_i            = '0;
            rs2_i            = '0;
            instruction_id   = '0;
            instruction      = '0;

            is_instruction_accepted = accept_instruction;

            if(accept_instruction) begin
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
    begin : commit_kill
        is_instruction_not_kill = 1;
        if(xif_commit.valid && xif_commit.commit.kill) begin
            if(instruction_id == xif_commit.commit.id) begin
                is_instruction_not_kill = 0;
            end
        end
    end

    // Results from AES functional unit
    always_ff @(posedge clk, negedge rst_n)
    begin : AES_FU_RESULTS
        if (rst_n == 1'b0)
        begin
            
        end else 
        begin
            if(xif_result.result_valid == 1 && xif_result.result_ready == 1)
                xif_result.result_valid = 0;

            if(ready_o) begin
                xif_result.result.id = id_in_aes_fu;
                xif_result.result.data      = rd_o;
                xif_result.result.rd        = rd_register_adr;
                xif_result.result.we        = 0;
                xif_result.result_valid     = 1;
            end
            
        end
    end


    riscv_crypto_fu_saes32 
    #(
        .SAES_DEC_EN ( 1 )                 // Enable saes32 decrypt instructions.
    )
    aes_i
    (
        .valid           (valid_aes_input)  , // Are the inputs valid?
        .rs1             (rs1_i)            , //[31:0] //! (modified) Key   
        .rs2             (rs2_i)            , //[31:0]//! Cipher 
        .bs              (byte_select_i)    , //[1:0]// Byte select immediate

        .op_saes32_encs  (encrypt_i)        , // Encrypt SubBytes
        .op_saes32_encsm (encrypt_middle_i) , // Encrypt SubBytes + MixColumn
        .op_saes32_decs  (decrypt_i)        , // Decrypt SubBytes
        .op_saes32_decsm (decrypt_middle_i) , // Decrypt SubBytes + MixColumn

        .rd              (result_aes_o)     , //[31:0]// output destination register value.
        .ready           (ready_aes_output)   // Compute finished?
    );





endmodule  // cv32e40x_xif_aes