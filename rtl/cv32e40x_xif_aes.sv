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


    logic valid_i, ready_i;
    logic encrypt_middle_i, encrypt_i, decrypt_i, decrypt_middle_i;
    logic [X_RFR_WIDTH-1:0] rs1_i, rs2_i, rd_i;
    logic [1:0] byte_select_i;
    logic [X_ID_WIDTH-1:0] id_in_aes_fu;



    // Accept offloaded instruction logic
    always_comb
    begin
        unique case(xif_issue.issue_req.instr[6:0])
            AES32: begin
                // accept instruction
                xif_issue.issue_resp.accept = 1;
                xif_issue.issue_resp.writeback = 1;
                xif_issue.issue_resp.dualwrite = 0;
                xif_issue.issue_resp.loadstore = 0;
                xif_issue.issue_resp.ecswrite = 0;
                xif_issue.issue_resp.exc = 0; //? what is a synchronous exception
            end
            default: begin
                //Dont accept instruction
                xif_issue.issue_resp.accept = 0;
                xif_issue.issue_resp.writeback = 0;
                xif_issue.issue_resp.dualwrite = 0;
                xif_issue.issue_resp.loadstore = 0;
                xif_issue.issue_resp.ecswrite = 0;
                xif_issue.issue_resp.exc = 0; //? what is a synchronous exception
            end
        endcase
    end

    always_ff @(posedge clk, negedge rst_n)
        begin : ID_FU_AES
        if (rst_n == 1'b0)
        begin
            rs1_i = '0;
            rs2_i = '0;
        end else 
        begin
            rs1_i            = '0;
            rs2_i            = '0;
            valid_i          = 1;
            decrypt_i        = 0;
            decrypt_middle_i = 0;
            encrypt_i        = 0;
            encrypt_middle_i = 0;

            id_in_aes_fu = xif_issue.issue_req.id;
            if(xif_issue.issue_req.rs_valid == 3'b??1)begin
                rs1_i = xif_issue.issue_req.rs[0];
            end else
            begin
                valid = 0;
            end

            if(xif_issue.issue_req.rs_valid == 3'b?1?)begin
                rs2_i = xif_issue.issue_req.rs[1];
            end else
            begin
                valid_i = 0;
            end

            byte_select = xif_issue.issue_req.instr[31:30];
            unique case(xif_issue.issue_req.instr[29:25])
                AES32DSI:  decrypt_i        = 1;
                AES32DSMI: decrypt_middle_i = 1;
                AES32ESI:  encrypt_i        = 1;
                AES32ESMI: encrypt_middle_i = 1;
            endcase
            rd_register_adr = xif_issue.issue_req.instr[11:7];

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
        .valid           (valid_i)          , // Are the inputs valid?
        .rs1             (rs1_i)            , //[31:0] //! (modified) Key   
        .rs2             (rs2_i)            , //[31:0]//! Cipher 
        .bs              (byte_select_i)    , //[1:0]// Byte select immediate

        .op_saes32_encs  (encrypt_i)        , // Encrypt SubBytes
        .op_saes32_encsm (encrypt_middle_i) , // Encrypt SubBytes + MixColumn
        .op_saes32_decs  (decrypt_i)        , // Decrypt SubBytes
        .op_saes32_decsm (decrypt_middle_i) , // Decrypt SubBytes + MixColumn

        .rd              (rd_o)             , //[31:0]// output destination register value.
        .ready           (ready_o)            // Compute finished?
    );





endmodule  // cv32e40x_xif_aes