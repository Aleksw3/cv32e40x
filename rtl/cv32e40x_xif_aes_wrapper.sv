module cv32e40x_xif_aes_wrapper import cv32e40x_pkg::*;
#(
  parameter int          X_ID_WIDTH      =  4,  // Width of ID field.
  parameter int          X_RFR_WIDTH     =  32, // Register file read access width for the eXtension interface
  parameter logic [ 1:0] X_ECS_XS        =  '0, // Default value for mstatus.XS
  parameter int          PROTECTED       =   1,
  parameter int          PIPELINE_STAGES =   5
)
(
  input  logic          clk_i,
  input  logic          rst_n,

  // eXtension interface
  if_xif.coproc_issue       xif_issue,         // Issue interface
  if_xif.coproc_commit      xif_commit,        // Commit Interface
  if_xif.coproc_result      xif_result         // Result interface
);
    //Output logic
    logic drop_instruction;
    logic enable_output_registers;
    logic ready_for_aes_output;


    //OUTPUT registers
    logic fu_output_valid;
    logic [31:0] fu_output_result;
    logic [X_ID_WIDTH-1:0] fu_output_instr_id;
    logic [5:0] fu_output_rd_adr;

    //FIFO accept
    logic fifo_flush, fifo_flush_but_first, test_mode;
    logic fifo_full_acc_instr, fifo_empty_acc_instr;
    logic fifo_push_acc_instr, fifo_pop_acc_instr;
    id_rd_packet_t fifo_data_push_acc_instr_i, fifo_data_pop_acc_instr_o;
    logic [PIPELINE_STAGES:0] fifo_cnt_acc_instr;

    // FIFO commit
    logic id_match;

    logic fifo_full_commit, fifo_empty_commit;
    logic fifo_push_commit, fifo_pop_commit;
    id_rd_packet_t fifo_data_pop_commit_o;
    logic [PIPELINE_STAGES:0] fifo_cnt_commit;

    //FIFO Kill
    logic fifo_full_kill, fifo_empty_kill;
    logic fifo_push_kill, fifo_pop_kill;
    id_rd_packet_t fifo_data_pop_kill_o;
    logic [PIPELINE_STAGES:0] fifo_cnt_kill;

    // Input logic
    logic valid_i, decrypt_i, encrypt_i, decrypt_middle_i, encrypt_middle_i;
    logic [X_ID_WIDTH-1:0]  aes_instr_id_o, instr_id_i;
    logic [X_RFR_WIDTH-1:0]  rs1_i, rs2_i, instr_i, result_aes_o;
    logic [35:0] randombits;




    logic valid_aes_input,  ready_aes_input;
    logic valid_aes_output, ready_aes_output;
    logic issue_ready;
    logic enable_input_registers;

    logic [1:0]              byte_select_i;
    logic [4:0]              xif_rd_adr;
    logic [6:0] xif_opcode;

    logic [7:0] shareB_rand;
    assign shareB_rand = 8'h02;

    //XIF Issue interface
    assign xif_issue.issue_ready = issue_ready;

    // XIF issue interface response
    assign xif_issue.issue_resp.accept    = enable_input_registers;
    assign xif_issue.issue_resp.writeback = 'b1;
    assign xif_issue.issue_resp.dualwrite = 'b0;
    assign xif_issue.issue_resp.dualread  = 'b0;
    assign xif_issue.issue_resp.loadstore = 'b0;
    assign xif_issue.issue_resp.ecswrite  = 'b0;
    assign xif_issue.issue_resp.exc       = 'b0;

    // XIF result interface
    assign xif_result.result_valid   = fu_output_valid;
    assign xif_result.result.data    = fu_output_result;
    assign xif_result.result.rd      = fu_output_rd_adr;
    assign xif_result.result.id      = fu_output_instr_id;
    assign xif_result.result.we      = 1'b1;
    assign xif_result.result.ecswe   = 1'b0;
    assign xif_result.result.ecsdata =   '0;
    assign xif_result.result.exc     = 1'b0;
    assign xif_result.result.exccode =   '0;


    assign xif_byte_select = xif_issue.issue_req.instr[31:30];
    assign xif_rd_adr      = xif_issue.issue_req.instr[11: 7];
    assign xif_opcode      = xif_issue.issue_req.instr[ 6: 0];
    assign byte_select_i   = instr_i[31:30];

    assign issue_ready = !valid_i || ready_aes_input;


    assign fifo_data_push_acc_instr_i = {xif_issue.issue_req.id, xif_rd_adr};
    assign fifo_push_acc_instr        = enable_input_registers;

    always_comb 
    begin : ACCEPT_INSTRUCTION
        enable_input_registers = 'b0;

        if(xif_opcode == AES32) begin
            if(xif_issue.issue_valid && issue_ready)
                enable_input_registers = 'b1;
        end    
    end

    always_ff @( posedge clk_i, negedge rst_n ) 
    begin : INPUT_STAGE_REGISTERS
        if(!rst_n) begin
            instr_i       = 'b0;
            rs1_i         = 'b0;
            rs2_i         = 'b0;
            valid_i       = 'b0;
        end else begin
            if(enable_input_registers)
            begin
                instr_i       = xif_issue.issue_req.instr;
                instr_id_i    = xif_issue.issue_req.id;
                rs1_i         = xif_issue.issue_req.rs[0];
                rs2_i         = xif_issue.issue_req.rs[1];
            end

            if(issue_ready)
                valid_i = enable_input_registers;
        end
    end

    always_comb
    begin : ONEHOT_AES_INSTR_TYPE
        decrypt_i        = 0;
        decrypt_middle_i = 0;
        encrypt_i        = 0;
        encrypt_middle_i = 0;
        unique case(instr_i[29:25])
            AES32DSI:  decrypt_i        = 1;
            AES32DSMI: decrypt_middle_i = 1;
            AES32ESI:  encrypt_i        = 1;
            AES32ESMI: encrypt_middle_i = 1;
        endcase
    end

    always_comb 
    begin : COMMIT_FIFO_LOGIC
        fifo_push_commit    = 'b0;
        fifo_push_kill      = 'b0;
        id_match            = 'b0; 
        fifo_pop_acc_instr  = 'b0;

        if(!fifo_empty_acc_instr)
            if(fifo_data_pop_acc_instr_o.instr_id == xif_commit.commit.id)
                id_match = 'b1;

        if(xif_commit.commit_valid && !xif_commit.commit.commit_kill)
            if(id_match)
                fifo_push_commit   = 'b1;

        else if(xif_commit.commit_valid && xif_commit.commit.commit_kill)
            if(id_match)
                fifo_push_kill = 'b1;

        if(fifo_push_kill || fifo_push_commit)
            fifo_pop_acc_instr = 'b1;
    end
    logic pop_commit_fifo;
    assign pop_commit_fifo = enable_output_registers & valid_aes_output;

    logic xif_ready;

    always_comb 
    begin : OUTPUT_STAGE_LOGIC
        // Accept new data in output stage?
        drop_instruction        = 'b0;
        enable_output_registers = 'b0;
        ready_for_aes_output = 'b0;

        if(aes_instr_id_o == fifo_data_pop_commit_o.instr_id)
            enable_output_registers = 'b1;

        else if(aes_instr_id_o == fifo_data_pop_kill_o.instr_id)
            drop_instruction = 'b1;
        
        // Is output stage ready for new output            
        if(!fu_output_valid || xif_ready || enable_output_registers)
            ready_for_aes_output = 'b1;
    end

    always_ff @( posedge clk_i, negedge rst_n  ) 
    begin : OUTPUT_REGISTERS
        if(!rst_n) begin
            fu_output_valid    = 'b0;
            fu_output_result   = 'b0;
            fu_output_instr_id = 'b0;
            fu_output_rd_adr   = 'b0;
        end else
        begin
            xif_ready = xif_result.result_ready;
            if(enable_output_registers)
            begin
                fu_output_result   = result_aes_o;
                fu_output_instr_id = aes_instr_id_o;
                fu_output_rd_adr   = fifo_data_pop_commit_o.rd_adr;
            end
            
            if(!fu_output_valid || xif_result.result_ready || enable_output_registers)
                fu_output_valid = valid_aes_output && !drop_instruction && enable_output_registers;

        end
    end

    // generate if(PROTECTED) begin: PREOTECTED_AES
        riscv_crypto_fu_saes32_protected
        #(
            .X_ID_WIDTH(X_ID_WIDTH)
        )
        aes_prot_i
        (
            .clk_i(clk_i)                           ,
            .rst_n(rst_n)                     ,
            .valid_i(valid_i)           ,
            .ready_i(ready_aes_input)           ,

            .rs1_i(rs1_i)                       , 
            .rs2_i(rs2_i)                       , 
            .shareB_mask_i(shareB_rand)              ,
            .randombits_i(randombits)           , 
            .instr_id_i(instr_id_i)             ,
            .bs_i(byte_select_i)                  ,

            .op_saes32_decs(decrypt_i)          ,
            .op_saes32_decsm(decrypt_middle_i)  ,
            .op_saes32_encs(encrypt_i)          ,
            .op_saes32_encsm(encrypt_middle_i)  ,

            .result_o(result_aes_o)             ,
            .instr_id_o(aes_instr_id_o)         ,
            .valid_o(valid_aes_output)       ,
            .ready_o(ready_for_aes_output)
        );

    // end else begin
    //     riscv_crypto_fu_saes32 
    //     #(
    //         .SAES_DEC_EN ( 1 )                 // Enable saes32 decrypt instructions.
    //     )
    //     aes_i
    //     (
    //         .valid           (valid_aes_input)  ,
    //         .rs1             (rs1_i)            , 
    //         .rs2             (rs2_i)            , 
    //         .bs              (byte_select_i)    ,

    //         .op_saes32_encs  (encrypt_i)        , // Encrypt SubBytes
    //         .op_saes32_encsm (encrypt_middle_i) , // Encrypt SubBytes + MixColumn
    //         .op_saes32_decs  (decrypt_i)        , // Decrypt SubBytes
    //         .op_saes32_decsm (decrypt_middle_i) , // Decrypt SubBytes + MixColumn

    //         .rd              (result_aes_o)     , // output destination register value.
    //         .ready           (ready_aes_output)   // Compute finished?
    //     );
    // end endgenerate


cv32e40x_fifo #(
     .DEPTH(PIPELINE_STAGES)
)
accepted_instruction_fifo_i
(
    .clk_i(clk_i),  
    .rst_ni(rst_n),  
    .flush_i(fifo_flush),
    .flush_but_first_i(fifo_flush_but_first),
    .testmode_i(test_mode),

    .full_o(fifo_full_acc_instr),
    .empty_o(fifo_empty_acc_instr),
    .cnt_o(fifo_cnt_acc_instr),

    .data_i(fifo_data_push_acc_instr_i),
    .push_i(enable_input_registers),

    .data_o(fifo_data_pop_acc_instr_o),
    .pop_i(fifo_pop_acc_instr)
);

cv32e40x_fifo #(
     .DEPTH(PIPELINE_STAGES)
)
commited_instruction_fifo_i
(
    .clk_i(clk_i),
    .rst_ni(rst_n),
    .flush_i(fifo_flush),
    .flush_but_first_i(fifo_flush_but_first),
    .testmode_i(test_mode), 

    .full_o(fifo_full_commit),
    .empty_o(fifo_empty_commit),
    .cnt_o(fifo_cnt_commit),

    .data_i(fifo_data_pop_acc_instr_o),
    .push_i(fifo_push_commit),

    .data_o(fifo_data_pop_commit_o),
    .pop_i(pop_commit_fifo)                
);

cv32e40x_fifo #(
     .DEPTH(PIPELINE_STAGES)
)
kill_instruction_fifo_i
(
    .clk_i(clk_i),
    .rst_ni(rst_n),
    .flush_i(fifo_flush),
    .flush_but_first_i(fifo_flush_but_first),
    .testmode_i(test_mode), 

    .full_o(fifo_full_kill),
    .empty_o(fifo_empty_kill),
    .cnt_o(fifo_cnt_kill),

    .data_i(fifo_data_pop_acc_instr_o),
    .push_i(fifo_push_kill),

    .data_o(fifo_data_pop_kill_o),
    .pop_i(drop_instruction)                
);


endmodule  // cv32e40x_xif_aes_wrapper