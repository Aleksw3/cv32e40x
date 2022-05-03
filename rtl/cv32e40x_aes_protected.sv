module riscv_crypto_fu_saes32_protected #(
    parameter SAES_DEC_EN = 1
)(
    input  wire         clk,
    input  wire         reset_n,
    input  wire         valid,

    input  wire [31:0]  rs1,
    input  wire [31:0]  rs2,
    input  wire [31:0]  rs3,
    input  wire [1:0]   bs,

    input  wire         op_saes32_decs,
    input  wire         op_saes32_decsm,
    input  wire         op_saes32_encs,
    input  wire         op_saes32_encsm,

    output wire [31:0] rd,
    output wire        ready
);

assign decrypt      = op_saes32_decs  || op_saes32_decsm;
assign middle_round = op_saes32_decsm || op_saes32_encsm;

wire [7:0] bytes_in_share_A [3:0];
assign bytes_in_share_A[0] = rs2[ 7: 0];
assign bytes_in_share_A[1] = rs2[15: 8];
assign bytes_in_share_A[2] = rs2[23:16];
assign bytes_in_share_A[3] = rs2[31:24];

wire [7:0] bytes_in_share_B [3:0];
assign bytes_in_share_B[0] = rs3[ 7: 0];
assign bytes_in_share_B[1] = rs3[15: 8];
assign bytes_in_share_B[2] = rs3[23:16];
assign bytes_in_share_B[3] = rs3[31:24];

assign byte_sel_share_A = bytes_in_share_A[bs];
assign byte_sel_share_B = bytes_in_share_B[bs];

// Mix Column GF(256) scalar multiplication functions
function [7:0] xtime2;
    input [7:0] byte_in;
    wire msb;
    wire [7:0] modulo;
    wire [7:0] byte_in_shifted;
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

wire [ 7:0] mix_b3_shareA =           xtimeN(sub_byte_share_A, (dec ? 11  : 3));
wire [ 7:0] mix_b2_shareA = decrypt ? xtimeN(sub_byte_share_A, (      13     )) : sub_byte_share_A;
wire [ 7:0] mix_b1_shareA = decrypt ? xtimeN(sub_byte_share_A, (       9     )) : sub_byte_share_A;
wire [ 7:0] mix_b0_shareA =           xtimeN(sub_byte_share_A, (dec ? 14  : 2));

wire [31:0] result_mix_shareA  = {mix_b3_shareA, mix_b2_shareA, mix_b1_shareA, mix_b0_shareA};
wire [31:0] result_shareA      = mix ? result_mix_shareA : {24'b0, sub_byte_share_A};

wire [ 7:0] mix_b3_shareB =           xtimeN(sub_byte_share_B, (decrypt ? 11  : 3));
wire [ 7:0] mix_b2_shareB = decrypt ? xtimeN(sub_byte_share_B, (          13     )) : sub_byte_share_B;
wire [ 7:0] mix_b1_shareB = decrypt ? xtimeN(sub_byte_share_B, (           9     )) : sub_byte_share_B;
wire [ 7:0] mix_b0_shareB =           xtimeN(sub_byte_share_B, (decrypt ? 14  : 2));

wire [31:0] result_mix_shareB  = {mix_b3_shareB, mix_b2_shareB, mix_b1_shareB, mix_b0_shareB};
wire [31:0] result_shareB      = middle_round ? result_mix_shareB : {24'b0, sub_byte_share_B};


wire [31:0] rotated_shareA     =
    {32{bs == 2'b00}} & {result_shareA                             } |
    {32{bs == 2'b01}} & {result_shareA[23:0], result_shareA[31:24] } |
    {32{bs == 2'b10}} & {result_shareA[15:0], result_shareA[31:16] } |
    {32{bs == 2'b11}} & {result_shareA[ 7:0], result_shareA[31: 8] } ;


wire [31:0] rotated_shareB     =
    {32{bs == 2'b00}} & {result_shareB                             } |
    {32{bs == 2'b01}} & {result_shareB[23:0], result_shareB[31:24] } |
    {32{bs == 2'b10}} & {result_shareB[15:0], result_shareB[31:16] } |
    {32{bs == 2'b11}} & {result_shareB[ 7:0], result_shareB[31: 8] } ;

assign key_addition_shareA = rotated_shareA ^ rs1;

assign rd = key_addition_shareA ^ rotated_shareB;

riscv_crypto_aes_dom_sbox i_aes_dom_sbox(
    .clk(clk),
    .reset_n(reset_n),

    .shareA_in(sel_byte_share_A),
    .shareB_in(sel_byte_share_A),

    .decrypt(decrypt),

    .shareA_out(sub_byte_share_A),
    .shareB_out(sub_byte_share_B)
);

// generate if(SAES_DEC_EN) begin: saes32_dec_sbox_implemented
// end else begin: saes32_dec_sbox_not_implemented
// end endgenerate;

endmodule