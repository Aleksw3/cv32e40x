module cv32e40x_dom_sbox #(

)(
    input wire clk,
    input wire reset_n,

    input wire [7:0] shareA_in,
    input wire [7:0] shareB_in,

    input wire decrypt,
    
    output wire [7:0] shareA_out,
    output wire [7:0] shareB_out
);


function [7:0] isomorphic_mapping;
input wire [7:0] byte_in;

wire [7:0] im;
im[7] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[2] ^ byte_in[1] ^ byte_in[0];
im[6] = byte_in[6] ^ byte_in[5] ^ byte_in[4] ^ byte_in[0];
im[5] = byte_in[6] ^ byte_in[5] ^ byte_in[1] ^ byte_in[0];
im[4] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[0];
im[3] = byte_in[7] ^ byte_in[4] ^ byte_in[3] ^ byte_in[1] ^ byte_in[0];
im[2] = byte_in[0];
im[1] = byte_in[6] ^ byte_in[5] ^ byte_in[0];
im[0] = byte_in[6] ^ byte_in[3] ^ byte_in[2] ^ byte_in[1] ^ byte_in[0];

isomorphic_mapping = im;
endfunction

function [7:0] inverse_isomorphic_mapping;
input wire [7:0] byte_in;

wire [7:0] im;
im[7] = byte_in[4] ^ byte_in[1];
im[6] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[3] ^ byte_in[1] ^ byte_in[0];
im[5] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[3] ^ byte_in[2] ^ byte_in[0];
im[4] = byte_in[6] ^ byte_in[1];
im[3] = byte_in[6] ^ byte_in[5] ^ byte_in[4] ^ byte_in[3] ^ byte_in[2] ^ byte_in[1];
im[2] = byte_in[7] ^ byte_in[5] ^ byte_in[4] ^ byte_in[1];
im[1] = byte_in[5] ^ byte_in[1];
im[0] = byte_in[2];

inverse_isomorphic_mapping = im;

endfunction

function [7:0] affine_transformation_addition;
input wire [7:0] byte_in;

wire [7:0] im;
im[7] = byte_in[7] ^ 0;
im[6] = byte_in[6] ^ 1;
im[5] = byte_in[5] ^ 1;
im[4] = byte_in[4] ^ 0;
im[3] = byte_in[3] ^ 0;
im[2] = byte_in[2] ^ 0;
im[1] = byte_in[1] ^ 1;
im[0] = byte_in[0] ^ 1;

affine_transformation_addition = im;

endfunction

function [7:0] affine_transformation_multiplication;
input wire [7:0] byte_in;

wire [7:0] im;
im[7] = byte_in[6] ^ byte_in[4] ^ byte_in[1];
im[6] = byte_in[5] ^ byte_in[3] ^ byte_in[0];
im[5] = byte_in[7] ^ byte_in[4] ^ byte_in[2];
im[4] = byte_in[6] ^ byte_in[3] ^ byte_in[1];
im[3] = byte_in[5] ^ byte_in[2] ^ byte_in[0];
im[2] = byte_in[7] ^ byte_in[4] ^ byte_in[1];
im[1] = byte_in[6] ^ byte_in[3] ^ byte_in[0];
im[0] = byte_in[7] ^ byte_in[5] ^ byte_in[2];

affine_transformation_multiplication = im;
endfunction

function [7:0] inverse_affine_transformation_addition;
input wire [7:0] byte_in;

wire [7:0] im;
im[7] = byte_in[7] ^ 0;
im[6] = byte_in[6] ^ 0;
im[5] = byte_in[5] ^ 0;
im[4] = byte_in[4] ^ 0;
im[3] = byte_in[3] ^ 0;
im[2] = byte_in[2] ^ 1;
im[1] = byte_in[1] ^ 0;
im[0] = byte_in[0] ^ 1;

inverse_affine_transformation_addition = im;
endfunction

function [7:0] inverse_affine_transformation_multiplication;
input wire [7:0] byte_in;

wire [7:0] im;
im[7] = byte_in[6] ^ byte_in[4] ^ byte_in[1];
im[6] = byte_in[5] ^ byte_in[3] ^ byte_in[0];
im[5] = byte_in[7] ^ byte_in[4] ^ byte_in[2];
im[4] = byte_in[6] ^ byte_in[3] ^ byte_in[1];
im[3] = byte_in[5] ^ byte_in[2] ^ byte_in[0];
im[2] = byte_in[7] ^ byte_in[4] ^ byte_in[1];
im[1] = byte_in[6] ^ byte_in[3] ^ byte_in[0];
im[0] = byte_in[7] ^ byte_in[5] ^ byte_in[2];

inverse_affine_transformation_multiplication = im;
endfunction

function [3:0] square_scale_gf16;
    input [3:0] nibble_in;
    
    wire [3:0] sum_bits       = nibble_in[3:2] ^ nibble_in[1:0];
    wire [3:0] square_sum     = square_gf4(sum_bits);
    wire [3:0] scale_h        = scale_N_gf4(nibble_in[3:2]);
    wire [3:0] square_scale_h = square_gf4(scale_h);

    square_scale_gf16 = {square_sum, square_scale_h};
end;

//! Probably need a register here
function [1:0][3:0] dom_multiplication_gf16;
    input [3:0] shareA_h_in;
    input [3:0] shareA_l_in;
    input [3:0] shareB_h_in;
    input [3:0] shareB_l_in;

    wire [3:0] AA_hl_mult = multiplication_gf16(shareA_h_in, shareA_l_in);
    wire [3:0] AB_hl_mult = multiplication_gf16(shareA_h_in, shareB_l_in);
    wire [3:0] BB_hl_mult = multiplication_gf16(shareB_h_in, shareB_l_in);
    wire [3:0] BA_hl_mult = multiplication_gf16(shareB_h_in, shareA_l_in);

    //TODO Implement randomness here
    `define random_value 4'ha
    wire [3:0] AB_hl_mult_r = AB_hl_mult ^ random_value;
    wire [3:0] BA_hl_mult_r = BA_hl_mult ^ random_value;

    wire [3:0] shareA_result = AA_hl_mult ^ AB_hl_mult_r;
    wire [3:0] shareB_result = BB_hl_mult ^ BA_hl_mult_r;

    dom_multiplication_gf16[0] = shareA_result;
    dom_multiplication_gf16[1] = shareB_result;
end;

function [3:0] multiplication_gf16;
    input [3:0] a_in;
    input [3:0] b_in;

    wire [1:0] a_sum = a_in[3:2] ^ a_in[1:0];
    wire [1:0] b_sum = b_in[3:2] ^ b_in[1:0];

    wire a_high_b_high_mult = multiplication_gf4(a_in[3:2], b_in[3:2]);
    wire a_low_b_low_mult   = multiplication_gf4(a_in[1:0], b_in[1:0]);
    wire ab_sum_mult        = multiplication_gf4(a_sum, b_sum);

    wire ab_sum_scale_N = scale_N_gf4(ab_sum_mult);

    wire result_h = ab_sum_scale_N ^ a_high_b_high_mult;
    wire result_l = ab_sum_scale_N ^ a_low_b_low_mult;

    multiplication_gf16 = {result_h, result_l};
endfunction

function [1:0][3:0] inversion_gf16;
    input [3:0] shareA_in;
    input [3:0] shareB_in;

    wire [1:0] shareA_sum = shareA_in[3:2] ^ shareA_in[1:0];
    wire [1:0] shareB_sum = shareB_in[3:2] ^ shareB_in[1:0];

    wire [1:0] shareA_square       = square_gf4(shareA_sum)
    wire [1:0] shareA_square_scale = scale_N_gf4(shareA_square)
    wire [1:0] shareB_square       = square_gf4(shareB_sum)
    wire [1:0] shareB_square_scale = scale_N_gf4(shareB_square)

    wire [1:0][1:0] multiply = dom_multiplication_gf4(shareA_in[3:2], shareA_in[1:0], shareB_in[3:2], shareB_in[1:0]);
    wire [1:0]shareA_multiply = multiply[0];
    wire [1:0]shareB_multiply = multiply[1];

    wire [1:0] shareA_sum_multiply = shareA_multiply ^ shareA_square_scale;
    wire [1:0] shareB_sum_multiply = shareB_multiply ^ shareB_square_scale;

    wire [1:0] shareA_inverted_sum = inverse_gf4(shareA_sum_multiply);
    wire [1:0] shareB_inverted_sum = inverse_gf4(shareB_sum_multiply);

    wire [1:0][1:0] result_h = dom_multiplication_gf4(shareA_in[1:0], shareA_inverted_sum, shareB_in[1:0], shareB_inverted_sum);
    wire [1:0][1:0] result_l = dom_multiplication_gf4(shareA_in[3:2], shareA_inverted_sum, shareB_in[3:2], shareB_inverted_sum);


    inversion_gf16[0] = {result_h[0], result_l[0]};
    inversion_gf16[1] = {result_h[1], result_l[1]};
end;

function [1:0] square_gf4;
    input bits_in;
    square_gf4 = {bits_in[0], bits_in[1]};
endfunction

function [1:0] inverse_gf4;
    input bits_in;
    inverse_gf4 = {bits_in[0], bits_in[1]};
endfunction

function [1:0] scale_N_gf4;
    input bits_in;
    scale_N_gf4 = {bits_in[0], bits_in[1] ^ bits_in[0]};
endfunction

//! Probably need a register here
//TODO check the order of the array parathesis
function [1:0][1:0] dom_multiplication_gf4;
    input [1:0] shareA_h_in;
    input [1:0] shareA_l_in;
    input [1:0] shareB_h_in;
    input [1:0] shareB_l_in;

    wire [1:0] AA_hl_mult = multiplication_gf4(shareA_h_in, shareA_l_in);
    wire [1:0] AB_hl_mult = multiplication_gf4(shareA_h_in, shareB_l_in);
    wire [1:0] BB_hl_mult = multiplication_gf4(shareB_h_in, shareB_l_in);
    wire [1:0] BA_hl_mult = multiplication_gf4(shareB_h_in, shareA_l_in);

    //TODO Implement randomness here
    `define random_value 2'b10
    wire [1:0] AB_hl_mult_r = AB_hl_mult ^ random_value;
    wire [1:0] BA_hl_mult_r = BA_hl_mult ^ random_value;

    wire [1:0] shareA_result = AA_hl_mult ^ AB_hl_mult_r;
    wire [1:0] shareB_result = BB_hl_mult ^ BA_hl_mult_r;

    dom_multiplication_gf4[0] = shareA_result;
    dom_multiplication_gf4[1] = shareB_result;
endfunction

function [1:0] multiplication_gf4;
    input [1:0] a_in;
    input [1:0] b_in;

    wire a_sum_bits = a_in[1] ^ a_in[0];
    wire b_sum_bits = b_in[1] ^ b_in[0];

    wire msb_ab_mult = a_in[1] & b_in[1];
    wire lsb_ab_mult = a_in[0] & b_in[0];
    wire a_sum_b_sum_mult = a_sum & b_sum;

    wire result_h = msb_ab_mult ^ a_sum_b_sum_mult;
    wire result_l = lsb_ab_mult ^ a_sum_b_sum_mult;

    multiplication_gf4 = {result_h, result_l};
endfunction



wire [7:0] shareA_isomorphic_trans;
wire [7:0] shareB_isomorphic_trans;
always_comb begin
    if(decrypt) begin
        shareA_isomorphic_trans = isomorphic_mapping(
                                    inverse_affine_transformation_addition(
                                        inverse_affine_transformation_multiplication(shareA_in)));

        shareB_isomorphic_trans = isomorphic_mapping(
                                    inverse_affine_transformation_multiplication(shareB_in));
    end else begin
        shareA_isomorphic_trans = isomorphic_mapping(shareA_in);
        shareB_isomorphic_trans = isomorphic_mapping(shareB_in);
    end
end

wire [7:0] shareA_result;
wire [7:0] shareB_result;
always_comb begin: GF256_inversion
    wire [3:0] shareA_sum_nibbles = shareA_isomorphic_trans[7:4] ^ shareA_isomorphic_trans[3:0];
    wire [3:0] shareB_sum_nibbles = shareB_isomorphic_trans[7:4] ^ shareB_isomorphic_trans[3:0];

    wire [3:0] shareA_square_scale = square_scale_gf16(shareA_sum_nibbles);
    wire [3:0] shareB_square_scale = square_scale_gf16(shareB_sum_nibbles);

    wire [7:0] multiplication = dom_multiplication_gf16(shareA_isomorphic_trans[7:4], 
                                                  shareA_isomorphic_trans[3:0],
                                                  shareB_isomorphic_trans[7:4], 
                                                  shareB_isomorphic_trans[3:0]);
    wire shareA_multiply = multiplication[7:4];
    wire shareB_multiply = multiplication[3:0];

    wire shareA_sum_multiply = shareA_multiply ^ shareA_sum_nibbles;
    wire shareB_sum_multiply = shareB_multiply ^ shareB_sum_nibbles;

    wire inverted = inversion_gf16(shareA_sum_multiply, shareB_sum_multiply);
    wire shareA_inverted = inverted[7:4];
    wire shareB_inverted = inverted[3:0];

    wire multiplication_high = dom_multiplication_gf16(shareA_isomorphic_trans[7:4], shareA_inverted, shareB_isomorphic_trans[7:4], shareB_inverted);
    wire multiplication_low  = dom_multiplication_gf16(shareA_isomorphic_trans[3:0], shareA_inverted, shareB_isomorphic_trans[3:0], shareB_inverted);
    
    shareA_result = {multiplication_high[7:4], multiplication_low[7:4]};
    shareB_result = {multiplication_high[3:0], multiplication_low[3:0]};
end

always_comb begin
    if(decode) begin
        shareA_out = inverse_isomorphic_mapping(shareA_result);
        shareB_out = inverse_isomorphic_mapping(shareB_result);
    end else begin
        shareA_out = inverse_isomorphic_mapping(
                            affine_transformation_addition(
                                affine_transformation_multiplication(shareA_result)));

        shareB_out = inverse_isomorphic_mapping(
                        affine_transformation_multiplication(shareB_result));
    end
end

endmodule