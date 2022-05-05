module cv32e40x_dom_sbox #(

)(
    input wire clk,
    input wire reset_n,

    input wire [7:0] shareA_in,
    input wire [7:0] shareB_in,

    input wire decrypt,
    
    output logic [7:0] shareA_out,
    output logic [7:0] shareB_out
);

function logic [7:0] isomorphic_mapping;
input [7:0] byte_in;

logic [7:0] im;
begin
    im[7] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[2] ^ byte_in[1] ^ byte_in[0];
    im[6] = byte_in[6] ^ byte_in[5] ^ byte_in[4] ^ byte_in[0];
    im[5] = byte_in[6] ^ byte_in[5] ^ byte_in[1] ^ byte_in[0];
    im[4] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[0];
    im[3] = byte_in[7] ^ byte_in[4] ^ byte_in[3] ^ byte_in[1] ^ byte_in[0];
    im[2] = byte_in[0];
    im[1] = byte_in[6] ^ byte_in[5] ^ byte_in[0];
    im[0] = byte_in[6] ^ byte_in[3] ^ byte_in[2] ^ byte_in[1] ^ byte_in[0];

    isomorphic_mapping = im;
end
endfunction

function logic [7:0] inverse_isomorphic_mapping;
input [7:0] byte_in;

logic [7:0] im;
begin
    im[7] = byte_in[4] ^ byte_in[1];
    im[6] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[3] ^ byte_in[1] ^ byte_in[0];
    im[5] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[3] ^ byte_in[2] ^ byte_in[0];
    im[4] = byte_in[6] ^ byte_in[1];
    im[3] = byte_in[6] ^ byte_in[5] ^ byte_in[4] ^ byte_in[3] ^ byte_in[2] ^ byte_in[1];
    im[2] = byte_in[7] ^ byte_in[5] ^ byte_in[4] ^ byte_in[1];
    im[1] = byte_in[5] ^ byte_in[1];
    im[0] = byte_in[2];

    inverse_isomorphic_mapping = im;
end

endfunction

function logic [7:0] affine_transformation_addition;
input [7:0] byte_in;

logic [7:0] im;
begin
    im[7] = byte_in[7] ^ 0;
    im[6] = byte_in[6] ^ 1;
    im[5] = byte_in[5] ^ 1;
    im[4] = byte_in[4] ^ 0;
    im[3] = byte_in[3] ^ 0;
    im[2] = byte_in[2] ^ 0;
    im[1] = byte_in[1] ^ 1;
    im[0] = byte_in[0] ^ 1;

    affine_transformation_addition = im;
end

endfunction

function logic [7:0] affine_transformation_multiplication;
input [7:0] byte_in;

logic [7:0] im;
begin
    im[7] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[4] ^ byte_in[3];
    im[6] = byte_in[6] ^ byte_in[5] ^ byte_in[4] ^ byte_in[3] ^ byte_in[2];
    im[5] = byte_in[5] ^ byte_in[4] ^ byte_in[3] ^ byte_in[2] ^ byte_in[1];
    im[4] = byte_in[4] ^ byte_in[3] ^ byte_in[2] ^ byte_in[1] ^ byte_in[0];
    im[3] = byte_in[7] ^ byte_in[3] ^ byte_in[2] ^ byte_in[1] ^ byte_in[0];
    im[2] = byte_in[7] ^ byte_in[6] ^ byte_in[2] ^ byte_in[1] ^ byte_in[0];
    im[1] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[1] ^ byte_in[0];
    im[0] = byte_in[7] ^ byte_in[6] ^ byte_in[5] ^ byte_in[4] ^ byte_in[0];

    affine_transformation_multiplication = im;
end
endfunction

function logic [7:0] inverse_affine_transformation_addition;
input  [7:0] byte_in;

logic [7:0] im;
begin
    im[7] = byte_in[7] ^ 0;
    im[6] = byte_in[6] ^ 0;
    im[5] = byte_in[5] ^ 0;
    im[4] = byte_in[4] ^ 0;
    im[3] = byte_in[3] ^ 0;
    im[2] = byte_in[2] ^ 1;
    im[1] = byte_in[1] ^ 0;
    im[0] = byte_in[0] ^ 1;

    inverse_affine_transformation_addition = im;
end
endfunction

function logic [7:0] inverse_affine_transformation_multiplication;
    input [7:0] byte_in;

    logic [7:0] im;
    begin
        im[7] = byte_in[6] ^ byte_in[4] ^ byte_in[1];
        im[6] = byte_in[5] ^ byte_in[3] ^ byte_in[0];
        im[5] = byte_in[7] ^ byte_in[4] ^ byte_in[2];
        im[4] = byte_in[6] ^ byte_in[3] ^ byte_in[1];
        im[3] = byte_in[5] ^ byte_in[2] ^ byte_in[0];
        im[2] = byte_in[7] ^ byte_in[4] ^ byte_in[1];
        im[1] = byte_in[6] ^ byte_in[3] ^ byte_in[0];
        im[0] = byte_in[7] ^ byte_in[5] ^ byte_in[2];

        inverse_affine_transformation_multiplication = im;
    end
endfunction

function logic [3:0] square_scale_gf16;
    input [3:0] nibble_in;
    logic [1:0] sum_bits;       
    logic [1:0] square_sum;     
    logic [1:0] scale_h;        
    logic [1:0] square_scale_h;
    begin
        sum_bits       = nibble_in[3:2] ^ nibble_in[1:0];
        square_sum     = square_gf4(sum_bits);
        scale_h        = scale_N_gf4(nibble_in[1:0]);
        square_scale_h = square_gf4(scale_h);

        square_scale_gf16 = {square_sum, square_scale_h};
    end
endfunction;

//! Probably need a register here
function logic [1:0][3:0] dom_multiplication_gf16;
    input [3:0] shareA_gf16_h_in;
    input [3:0] shareA_gf16_l_in;
    input [3:0] shareB_gf16_h_in;
    input [3:0] shareB_gf16_l_in;
    logic [3:0] AA_hl_mult; 
    logic [3:0] AB_hl_mult; 
    logic [3:0] BB_hl_mult; 
    logic [3:0] BA_hl_mult; 
    logic [3:0] AB_hl_mult_r;
    logic [3:0] BA_hl_mult_r;
    logic [3:0] shareA_result;
    logic [3:0] shareB_result;

    begin 
        
        AA_hl_mult = multiplication_gf16_1(shareA_gf16_h_in, shareA_gf16_l_in);
        AB_hl_mult = multiplication_gf16_2(shareA_gf16_h_in, shareB_gf16_l_in);
        BB_hl_mult = multiplication_gf16_3(shareB_gf16_h_in, shareB_gf16_l_in);
        BA_hl_mult = multiplication_gf16_4(shareB_gf16_h_in, shareA_gf16_l_in);

        //TODO Implement randomness here
        `define random_value 4'ha

        AB_hl_mult_r = AB_hl_mult ^ `random_value;
        BA_hl_mult_r = BA_hl_mult ^ `random_value;

        shareA_result = AA_hl_mult ^ AB_hl_mult_r;
        shareB_result = BB_hl_mult ^ BA_hl_mult_r;

        dom_multiplication_gf16[0] = shareA_result;
        dom_multiplication_gf16[1] = shareB_result;
    end
endfunction;

function logic [3:0] multiplication_gf16_1;
    input [3:0] a_in;
    input [3:0] b_in;

    logic [1:0] a_sum;
    logic [1:0] b_sum;
    logic [1:0] a_high_b_high_mult; 
    logic [1:0] a_low_b_low_mult;   
    logic [1:0] ab_sum_mult;        
    logic [1:0] ab_sum_scale_N; 
    logic [1:0] result_h; 
    logic [1:0] result_l; 
    begin
        a_sum = a_in[3:2] ^ a_in[1:0];
        b_sum = b_in[3:2] ^ b_in[1:0];

        a_high_b_high_mult = multiplication_gf4_1(a_in[3:2], b_in[3:2]);
        a_low_b_low_mult   = multiplication_gf4_2(a_in[1:0], b_in[1:0]);
        ab_sum_mult        = multiplication_gf4_3(a_sum, b_sum);

        ab_sum_scale_N = scale_N_gf4(ab_sum_mult);

        result_h = ab_sum_scale_N ^ a_high_b_high_mult;
        result_l = ab_sum_scale_N ^ a_low_b_low_mult;

        multiplication_gf16_1 = {result_h, result_l};
    end
endfunction

function logic [3:0] multiplication_gf16_2;
    input [3:0] a_in;
    input [3:0] b_in;

    logic [1:0] a_sum;
    logic [1:0] b_sum;
    logic [1:0] a_high_b_high_mult; 
    logic [1:0] a_low_b_low_mult;   
    logic [1:0] ab_sum_mult;        
    logic [1:0] ab_sum_scale_N; 
    logic [1:0] result_h; 
    logic [1:0] result_l; 
    begin
        a_sum = a_in[3:2] ^ a_in[1:0];
        b_sum = b_in[3:2] ^ b_in[1:0];

        a_high_b_high_mult = multiplication_gf4(a_in[3:2], b_in[3:2]);
        a_low_b_low_mult   = multiplication_gf4(a_in[1:0], b_in[1:0]);
        ab_sum_mult        = multiplication_gf4(a_sum, b_sum);

        ab_sum_scale_N = scale_N_gf4(ab_sum_mult);

        result_h = ab_sum_scale_N ^ a_high_b_high_mult;
        result_l = ab_sum_scale_N ^ a_low_b_low_mult;

        multiplication_gf16_2 = {result_h, result_l};
    end
endfunction

function logic [3:0] multiplication_gf16_3;
    input [3:0] a_in;
    input [3:0] b_in;

    logic [1:0] a_sum;
    logic [1:0] b_sum;
    logic [1:0] a_high_b_high_mult; 
    logic [1:0] a_low_b_low_mult;   
    logic [1:0] ab_sum_mult;        
    logic [1:0] ab_sum_scale_N; 
    logic [1:0] result_h; 
    logic [1:0] result_l; 
    begin
        a_sum = a_in[3:2] ^ a_in[1:0];
        b_sum = b_in[3:2] ^ b_in[1:0];

        a_high_b_high_mult = multiplication_gf4(a_in[3:2], b_in[3:2]);
        a_low_b_low_mult   = multiplication_gf4(a_in[1:0], b_in[1:0]);
        ab_sum_mult        = multiplication_gf4(a_sum, b_sum);

        ab_sum_scale_N = scale_N_gf4(ab_sum_mult);

        result_h = ab_sum_scale_N ^ a_high_b_high_mult;
        result_l = ab_sum_scale_N ^ a_low_b_low_mult;

        multiplication_gf16_3 = {result_h, result_l};
    end
endfunction

function logic [3:0] multiplication_gf16_4;
    input [3:0] a_in;
    input [3:0] b_in;

    logic [1:0] a_sum;
    logic [1:0] b_sum;
    logic [1:0] a_high_b_high_mult; 
    logic [1:0] a_low_b_low_mult;   
    logic [1:0] ab_sum_mult;        
    logic [1:0] ab_sum_scale_N; 
    logic [1:0] result_h; 
    logic [1:0] result_l; 
    begin
        a_sum = a_in[3:2] ^ a_in[1:0];
        b_sum = b_in[3:2] ^ b_in[1:0];

        a_high_b_high_mult = multiplication_gf4(a_in[3:2], b_in[3:2]);
        a_low_b_low_mult   = multiplication_gf4(a_in[1:0], b_in[1:0]);
        ab_sum_mult        = multiplication_gf4(a_sum, b_sum);

        ab_sum_scale_N = scale_N_gf4(ab_sum_mult);

        result_h = ab_sum_scale_N ^ a_high_b_high_mult;
        result_l = ab_sum_scale_N ^ a_low_b_low_mult;

        multiplication_gf16_4 = {result_h, result_l};
    end
endfunction

function logic [1:0][3:0] inversion_gf16;
    input [3:0] shareA_in;
    input [3:0] shareB_in;
    
    logic [1:0] shareA_sum;
    logic [1:0] shareB_sum;
    logic [1:0] shareA_square;
    logic [1:0] shareA_square_scale;
    logic [1:0] shareB_square;
    logic [1:0] shareB_square_scale;
    logic [1:0][1:0] multiply;
    logic [1:0]shareA_multiply;
    logic [1:0]shareB_multiply;
    logic [1:0] shareA_sum_multiply;
    logic [1:0] shareB_sum_multiply;
    logic [1:0] shareA_inverted_sum;
    logic [1:0] shareB_inverted_sum;
    logic [1:0][1:0] result_h;
    logic [1:0][1:0] result_l;
    begin
        shareA_sum = shareA_in[3:2] ^ shareA_in[1:0];
        shareB_sum = shareB_in[3:2] ^ shareB_in[1:0];

        shareA_square       = square_gf4(shareA_sum);
        shareA_square_scale = scale_N_gf4(shareA_square);
        shareB_square       = square_gf4(shareB_sum);
        shareB_square_scale = scale_N_gf4(shareB_square);

        multiply = dom_multiplication_gf4(shareA_in[3:2], shareA_in[1:0], shareB_in[3:2], shareB_in[1:0]);
        shareA_multiply = multiply[0];
        shareB_multiply = multiply[1];

        shareA_sum_multiply = shareA_multiply ^ shareA_square_scale;
        shareB_sum_multiply = shareB_multiply ^ shareB_square_scale;

        shareA_inverted_sum = inverse_gf4(shareA_sum_multiply);
        shareB_inverted_sum = inverse_gf4(shareB_sum_multiply);

        result_h = dom_multiplication_gf4(shareA_in[1:0], shareA_inverted_sum, shareB_in[1:0], shareB_inverted_sum);
        result_l = dom_multiplication_gf4(shareA_in[3:2], shareA_inverted_sum, shareB_in[3:2], shareB_inverted_sum);


        inversion_gf16[0] = {result_h[0], result_l[0]};
        inversion_gf16[1] = {result_h[1], result_l[1]};
    end
endfunction;

function logic [1:0] square_gf4;
    input [1:0] bits_in;
    square_gf4 = {bits_in[0], bits_in[1]};
endfunction

function logic [1:0] inverse_gf4;
    input [1:0] bits_in;
    inverse_gf4 = {bits_in[0], bits_in[1]};
endfunction

function logic [1:0] scale_N_gf4;
    input [1:0] bits_in;
    scale_N_gf4 = {bits_in[0], bits_in[1] ^ bits_in[0]};
endfunction

//! Probably need a register here
function logic [1:0][1:0] dom_multiplication_gf4;
    input [1:0] shareA_h_in;
    input [1:0] shareA_l_in;
    input [1:0] shareB_h_in;
    input [1:0] shareB_l_in;
    logic [1:0] AA_hl_mult;
    logic [1:0] AB_hl_mult;
    logic [1:0] BB_hl_mult;
    logic [1:0] BA_hl_mult;
    logic [1:0] AB_hl_mult_r;
    logic [1:0] BA_hl_mult_r;
    logic [1:0] shareA_result;
    logic [1:0] shareB_result;
    begin
        AA_hl_mult = multiplication_gf4(shareA_h_in, shareA_l_in);
        AB_hl_mult = multiplication_gf4(shareA_h_in, shareB_l_in);
        BB_hl_mult = multiplication_gf4(shareB_h_in, shareB_l_in);
        BA_hl_mult = multiplication_gf4(shareB_h_in, shareA_l_in);

        //TODO Implement randomness here
        `define random_value2 2'b10
        AB_hl_mult_r = AB_hl_mult ^ `random_value2;
        BA_hl_mult_r = BA_hl_mult ^ `random_value2;

        shareA_result = AA_hl_mult ^ AB_hl_mult_r;
        shareB_result = BB_hl_mult ^ BA_hl_mult_r;

        dom_multiplication_gf4[0] = shareA_result;
        dom_multiplication_gf4[1] = shareB_result;
    end
endfunction

function logic [1:0] multiplication_gf4;
    input [1:0] a_in;
    input [1:0] b_in;
    logic a_sum_bits;
    logic b_sum_bits;
    logic msb_ab_mult;
    logic lsb_ab_mult;
    logic a_sum_b_sum_mult;
    logic result_h;
    logic result_l;
    begin
        a_sum_bits = a_in[1] ^ a_in[0]; 
        b_sum_bits = b_in[1] ^ b_in[0]; 

        msb_ab_mult = a_in[1] & b_in[1]; 
        lsb_ab_mult = a_in[0] & b_in[0]; 
        a_sum_b_sum_mult = a_sum_bits & b_sum_bits; 

        result_h = msb_ab_mult ^ a_sum_b_sum_mult; 
        result_l = lsb_ab_mult ^ a_sum_b_sum_mult; 

        multiplication_gf4 = {result_h, result_l};
    end
endfunction

function logic [1:0] multiplication_gf4_1;
    input [1:0] a_in;
    input [1:0] b_in;
    logic a_sum_bits;
    logic b_sum_bits;
    logic msb_ab_mult;
    logic lsb_ab_mult;
    logic a_sum_b_sum_mult;
    logic result_h;
    logic result_l;
    begin
        a_sum_bits = a_in[1] ^ a_in[0]; 
        b_sum_bits = b_in[1] ^ b_in[0]; 

        msb_ab_mult = a_in[1] & b_in[1]; 
        lsb_ab_mult = a_in[0] & b_in[0]; 
        a_sum_b_sum_mult = a_sum_bits & b_sum_bits; 

        result_h = msb_ab_mult ^ a_sum_b_sum_mult; 
        result_l = lsb_ab_mult ^ a_sum_b_sum_mult; 

        multiplication_gf4_1 = {result_h, result_l};
    end
endfunction

function logic [1:0] multiplication_gf4_2;
    input [1:0] a_in;
    input [1:0] b_in;
    logic a_sum_bits;
    logic b_sum_bits;
    logic msb_ab_mult;
    logic lsb_ab_mult;
    logic a_sum_b_sum_mult;
    logic result_h;
    logic result_l;
    begin
        a_sum_bits = a_in[1] ^ a_in[0]; 
        b_sum_bits = b_in[1] ^ b_in[0]; 

        msb_ab_mult = a_in[1] & b_in[1]; 
        lsb_ab_mult = a_in[0] & b_in[0]; 
        a_sum_b_sum_mult = a_sum_bits & b_sum_bits; 

        result_h = msb_ab_mult ^ a_sum_b_sum_mult; 
        result_l = lsb_ab_mult ^ a_sum_b_sum_mult; 

        multiplication_gf4_2 = {result_h, result_l};
    end
endfunction

function logic [1:0] multiplication_gf4_3;
    input [1:0] a_in;
    input [1:0] b_in;
    logic a_sum_bits;
    logic b_sum_bits;
    logic msb_ab_mult;
    logic lsb_ab_mult;
    logic a_sum_b_sum_mult;
    logic result_h;
    logic result_l;
    begin
        a_sum_bits = a_in[1] ^ a_in[0]; 
        b_sum_bits = b_in[1] ^ b_in[0]; 

        msb_ab_mult = a_in[1] & b_in[1]; 
        lsb_ab_mult = a_in[0] & b_in[0]; 
        a_sum_b_sum_mult = a_sum_bits & b_sum_bits; 

        result_h = msb_ab_mult ^ a_sum_b_sum_mult; 
        result_l = lsb_ab_mult ^ a_sum_b_sum_mult; 

        multiplication_gf4_3 = {result_h, result_l};
    end
endfunction





logic [7:0] shareA_isomorphic_trans;
logic [7:0] shareB_isomorphic_trans;
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

logic [7:0] shareA_result;
logic [7:0] shareB_result;
logic [3:0] shareA_sum_nibbles; 
logic [3:0] shareB_sum_nibbles; 
logic [3:0] shareA_square_scale; 
logic [3:0] shareB_square_scale; 
logic [1:0][3:0] multiplication; 
logic [3:0] shareA_multiply;
logic [3:0] shareB_multiply;
logic [3:0] shareA_sum_multiply;
logic [3:0] shareB_sum_multiply;
logic [1:0][3:0] inverted;
logic [3:0] shareA_inverted;
logic [3:0] shareB_inverted;
logic [1:0][3:0] multiplication_high;
logic [1:0][3:0] multiplication_low;
logic [3:0] sharea_h, sharea_l, shareb_h, shareb_l;

always_comb 
begin: GF256_inversion
    shareA_sum_nibbles = shareA_isomorphic_trans[7:4] ^ shareA_isomorphic_trans[3:0];
    shareB_sum_nibbles = shareB_isomorphic_trans[7:4] ^ shareB_isomorphic_trans[3:0];

    shareA_square_scale = square_scale_gf16(shareA_sum_nibbles);
    shareB_square_scale = square_scale_gf16(shareB_sum_nibbles);

    sharea_h = shareA_isomorphic_trans[7:4];
    sharea_l = shareA_isomorphic_trans[3:0];
    shareb_h = shareB_isomorphic_trans[7:4];
    shareb_l = shareB_isomorphic_trans[3:0];

    multiplication = dom_multiplication_gf16(sharea_h, 
                                             sharea_l,
                                             shareb_h, 
                                             shareb_l);

    shareA_multiply = multiplication[0];
    shareB_multiply = multiplication[1];

    shareA_sum_multiply = shareA_multiply ^ shareA_square_scale;
    shareB_sum_multiply = shareB_multiply ^ shareB_square_scale;

    inverted = inversion_gf16(shareA_sum_multiply, shareB_sum_multiply);
    shareA_inverted = inverted[0];
    shareB_inverted = inverted[1];

    multiplication_high = dom_multiplication_gf16(shareA_isomorphic_trans[3:0], 
                                                    shareA_inverted, 
                                                    shareB_isomorphic_trans[3:0], 
                                                    shareB_inverted);
    multiplication_low  = dom_multiplication_gf16(shareA_isomorphic_trans[7:4], 
                                                    shareA_inverted, 
                                                    shareB_isomorphic_trans[7:4], 
                                                    shareB_inverted);
    
    shareA_result = {multiplication_high[0], multiplication_low[0]};
    shareB_result = {multiplication_high[1], multiplication_low[1]};
end
logic [7:0] a1, a2;
logic [7:0] b1;

always_comb begin
    // if(decrypt == 'b1) begin
    //     shareA_out = inverse_isomorphic_mapping(shareA_result);
    //     shareB_out = inverse_isomorphic_mapping(shareB_result);
    // end else begin
        a1 = inverse_isomorphic_mapping(shareA_result);
        a2 = affine_transformation_multiplication(a1);
        shareA_out = affine_transformation_addition(a2);
                            
                                
        b1 = inverse_isomorphic_mapping(shareB_result);
        shareB_out = affine_transformation_multiplication(b1);
    // end

end

endmodule