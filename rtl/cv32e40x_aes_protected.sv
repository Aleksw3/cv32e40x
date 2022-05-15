module riscv_crypto_fu_saes32_protected 
#(
    parameter int          X_ID_WIDTH      =  4  // Width of ID field.
)
(
    input  wire         clk,
    input  wire         reset_n,
    input  wire         valid_i,
    output  wire        ready_i,
    input  

    input  wire [31:0]  rs1_i,
    input  wire [31:0]  rs2_i,
    input  wire [7: 0]  shareB_mask_i, // 8-bits of random fetched from an RNG generator
    input  wire [35:0]  randombits_i, // Randomnbits required by the masked SBox implementation to remask certain operations
    input  wire [ID_LENGTH-1:0]  instr_id_i,
    input  wire [1: 0]  bs_i,

    input  wire         op_saes32_decs,
    input  wire         op_saes32_decsm,
    input  wire         op_saes32_encs,
    input  wire         op_saes32_encsm,


    output wire [31:0] result_o,
    output wire [ID_LENGTH-1:0] instr_id_o,
    output wire        valid_o,
    input  wire        ready_o
);
wire [7:0] sub_byte_shareA, sub_byte_shareB;
logic [31:0] add_round_key_shareA;
logic decrypt_i, middle_round_i;

//! TEMPORARY SOLUTION THAT WORKS FOR SIMULATION 
//! DOES NOT WORK FOR PIPELINED DESIGN!!
// assign ready_i = valid;

assign decrypt_i      = op_saes32_decs  || op_saes32_decsm;
assign middle_round_i = op_saes32_decsm || op_saes32_encsm;

/*//? [1]
It is possible to encrypt and decrypt using the the original implementation where the indeces of the bytes are flipped and the word is not rotated at the end,
however, this does not produce the same result as in the standard. Thus, another implementation would not be able to decrypt the message if it is not using the same
implementation as we do. 
We are, therefore, using the approach that produce the same results as the standard expects.
*/
wire [7:0] bytes_in_shareA [3:0];
assign bytes_in_shareA[3] = rs2_i[ 7: 0];
assign bytes_in_shareA[2] = rs2_i[15: 8];
assign bytes_in_shareA[1] = rs2_i[23:16];
assign bytes_in_shareA[0] = rs2_i[31:24];

logic [7:0] byte_sel_shareA;
assign byte_sel_shareA = bytes_in_shareA[bs];

//TODO need to save values in registers
logic [7:0] shareA_masked_i;
assign shareA_masked_i = byte_sel_shareA ^ shareB_i;


// Mix Column GF(256) scalar multiplication functions
function [7:0] xtime2;
    input [7:0] byte_in;
    logic msb;
    logic [7:0] modulo;
    logic [7:0] byte_in_shifted;
    begin
        msb = byte_in[7];
        modulo = msb ? 8'h1b : 8'b0;
        byte_in_shifted = {byte_in[6:0], 1'b0};
        
        xtime2  = byte_in_shifted ^ modulo;
    end
endfunction

function [7:0] xtimeN;
    input[7:0] byte_in;
    input[3:0] scalar;

    xtimeN = 
        (scalar[0] ?                       byte_in   : 0) ^
        (scalar[1] ? xtime2(               byte_in)  : 0) ^
        (scalar[2] ? xtime2(xtime2(        byte_in)) : 0) ^
        (scalar[3] ? xtime2(xtime2(xtime2( byte_in))): 0) ;
endfunction

wire [ 7:0] mix_b3_shareA =           xtimeN(sub_byte_shareA, (decrypt ? 11 : 3));
wire [ 7:0] mix_b2_shareA = decrypt ? xtimeN(sub_byte_shareA, (          13   )) : sub_byte_shareA;
wire [ 7:0] mix_b1_shareA = decrypt ? xtimeN(sub_byte_shareA, (           9   )) : sub_byte_shareA;
wire [ 7:0] mix_b0_shareA =           xtimeN(sub_byte_shareA, (decrypt ? 14 : 2));

wire [31:0] result_mix_shareA  = {mix_b3_shareA, mix_b2_shareA, mix_b1_shareA, mix_b0_shareA};
wire [31:0] result_shareA      = middle_round ? result_mix_shareA : {24'b0, sub_byte_shareA};


wire [ 7:0] mix_b3_shareB =           xtimeN(sub_byte_shareB, (decrypt ? 11 : 3));
wire [ 7:0] mix_b2_shareB = decrypt ? xtimeN(sub_byte_shareB, (          13    )) : sub_byte_shareB;
wire [ 7:0] mix_b1_shareB = decrypt ? xtimeN(sub_byte_shareB, (           9    )) : sub_byte_shareB;
wire [ 7:0] mix_b0_shareB =           xtimeN(sub_byte_shareB, (decrypt ? 14 : 2));

wire [31:0] result_mix_shareB  = {mix_b3_shareB, mix_b2_shareB, mix_b1_shareB, mix_b0_shareB};
wire [31:0] result_shareB      = middle_round ? result_mix_shareB : {24'b0, sub_byte_shareB};


wire [31:0] rotated_shareA_tmp     =
    {32{bs == 2'b00}} & {result_shareA                             } |
    {32{bs == 2'b01}} & {result_shareA[23:0], result_shareA[31:24] } |
    {32{bs == 2'b10}} & {result_shareA[15:0], result_shareA[31:16] } |
    {32{bs == 2'b11}} & {result_shareA[ 7:0], result_shareA[31: 8] } ;
//? Ref comment [1]
wire [31:0] rotated_shareA = {rotated_shareA_tmp[7:0], rotated_shareA_tmp[15:8], rotated_shareA_tmp[23:16], rotated_shareA_tmp[31:24]};


wire [31:0] rotated_shareB_tmp     =
    {32{bs == 2'b00}} & {result_shareB                             } |
    {32{bs == 2'b01}} & {result_shareB[23:0], result_shareB[31:24] } |
    {32{bs == 2'b10}} & {result_shareB[15:0], result_shareB[31:16] } |
    {32{bs == 2'b11}} & {result_shareB[ 7:0], result_shareB[31: 8] } ;
wire [31:0] rotated_shareB = {rotated_shareB_tmp[7:0], rotated_shareB_tmp[15:8], rotated_shareB_tmp[23:16], rotated_shareB_tmp[31:24]};

assign add_round_key_shareA = rotated_shareA ^ rs1;
assign result_o = add_round_key_shareA ^ rotated_shareB;

logic sbox_ready;
logic sbox_valid_o, aes_ready_o;
logic valid_input, decrypt, middle_round;
logic [31:0] rs1, rs2;
logic [35:0] randombits;
logic [7: 0] shareB, shareA_masked; 
logic [1: 0] bs;
logic [ID_LENGTH-1:0] instr_id,


assign ready_i = !valid_input || sbox_ready;

always_ff @( posedge clk, negedge rst_n ) 
begin : AES_INPUT_REGISTERS
    if(!reset_n)
    begin

    end else begin
        if(sbox_ready || !valid_input) 
        begin
            valid_input   = valid_i;
            rs2           = rs2_i;
            bs            = bs_i;
            shareA_masked = shareA_masked_i;
            shareB_mask   = shareB_mask_i;
            randombits    = randombits_i;
            instr_id      = instr_id_i;
            decrypt       = decrypt_i;
            middle_round  = middle_round_i;
        end
    end    
end

assign valid_o     = sbox_valid_o;
assign aes_ready_o = ready_o;

cv32e40x_dom_sbox i_aes_dom_sbox
#(
    .X_ID_WIDTH(X_ID_WIDTH)
)
(
    .clk(clk),
    .reset_n(reset_n),
    .valid_i(valid_input),
    .ready_for_sbox_i(sbox_ready),
    .instr_id_i(instr_id), 

    .shareA_in(shareA_masked),
    .shareB_in(shareB_mask),
    .randombits(randombits),

    .decrypt(decrypt),
    .middle_round(middle_round),
    .bs(bs),

    .valid_o(sbox_valid_o),
    .ready_for_sbox_o(aes_ready_o),
    .instr_id_o(instr_id_o), 
    .shareA_out(sub_byte_shareA),
    .shareB_out(sub_byte_shareB)
);

endmodule