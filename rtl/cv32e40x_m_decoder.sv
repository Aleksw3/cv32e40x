// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer        Oivind Ekelund- oivind.ekelund@silabs.com                  //
//                                                                            //
// Design Name:    M Decoder                                                    //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder for the M extension                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_m_decoder import cv32e40x_pkg::*;
  (
   // from IF/ID pipeline
   input logic [31:0] instr_rdata_i,

   output             decoder_ctrl_t decoder_ctrl_o
   );
  
  always_comb
  begin

    decoder_ctrl_o = DECODER_CTRL_IDLE;

    unique case (instr_rdata_i[6:0])
      
      //////////////////////////
      //     _    _    _   _  //
      //    / \  | |  | | | | //
      //   / _ \ | |  | | | | //
      //  / ___ \| |__| |_| | //
      // /_/   \_\_____\___/  //
      //                      //
      //////////////////////////
      
      OPCODE_OP: begin  // Register-Register ALU operation

        // PREFIX 11
        if (instr_rdata_i[31:30] == 2'b11) begin
            decoder_ctrl_o.illegal_insn_o = 1'b1;
        end

        // PREFIX 10
        else if (instr_rdata_i[31:30] == 2'b10) begin
          decoder_ctrl_o.illegal_insn_o = 1'b1;
        end  // prefix 10

        // PREFIX 00/01
        else begin
          decoder_ctrl_o.rf_we          = 1'b1;
          decoder_ctrl_o.rf_re_o[0]     = 1'b1;

          if (~instr_rdata_i[28]) decoder_ctrl_o.rf_re_o[1] = 1'b1;

          unique case ({instr_rdata_i[30:25], instr_rdata_i[14:12]})
            
            // supported RV32M instructions
            {6'b00_0001, 3'b000}: begin // mul
              decoder_ctrl_o.match           = 1'b1;
              decoder_ctrl_o.alu_en          = 1'b0;
              decoder_ctrl_o.mult_en         = 1'b1;
              decoder_ctrl_o.mult_operator_o = MUL_M32;
            end
            {6'b00_0001, 3'b001}: begin // mulh
              decoder_ctrl_o.match              = 1'b1;
              decoder_ctrl_o.alu_en             = 1'b0;
              decoder_ctrl_o.mult_signed_mode_o = 2'b11;
              decoder_ctrl_o.mult_en            = 1'b1;
              decoder_ctrl_o.mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b010}: begin // mulhsu
              decoder_ctrl_o.match              = 1'b1;
              decoder_ctrl_o.alu_en             = 1'b0;
              decoder_ctrl_o.mult_signed_mode_o = 2'b01;
              decoder_ctrl_o.mult_en            = 1'b1;
              decoder_ctrl_o.mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b011}: begin // mulhu
              decoder_ctrl_o.match              = 1'b1;
              decoder_ctrl_o.alu_en             = 1'b0;
              decoder_ctrl_o.mult_signed_mode_o = 2'b00;
              decoder_ctrl_o.mult_en            = 1'b1;
              decoder_ctrl_o.mult_operator_o    = MUL_H;
            end
            {6'b00_0001, 3'b100}: begin // div
              decoder_ctrl_o.match              = 1'b1;
              decoder_ctrl_o.alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              decoder_ctrl_o.alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              decoder_ctrl_o.rf_re_o[1]         = 1'b1;
              decoder_ctrl_o.alu_operator_o     = ALU_DIV;
            end
            {6'b00_0001, 3'b101}: begin // divu
              decoder_ctrl_o.match              = 1'b1;
              decoder_ctrl_o.alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              decoder_ctrl_o.alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              decoder_ctrl_o.rf_re_o[1]         = 1'b1;
              decoder_ctrl_o.alu_operator_o     = ALU_DIVU;
            end
            {6'b00_0001, 3'b110}: begin // rem
              decoder_ctrl_o.match              = 1'b1;
              decoder_ctrl_o.alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              decoder_ctrl_o.alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              decoder_ctrl_o.rf_re_o[1]         = 1'b1;
              decoder_ctrl_o.alu_operator_o     = ALU_REM;
            end
            {6'b00_0001, 3'b111}: begin // remu
              decoder_ctrl_o.match              = 1'b1;
              decoder_ctrl_o.alu_op_a_mux_sel_o = OP_A_REGB_OR_FWD;
              decoder_ctrl_o.alu_op_b_mux_sel_o = OP_B_REGA_OR_FWD;
              decoder_ctrl_o.rf_re_o[1]         = 1'b1;
              decoder_ctrl_o.alu_operator_o     = ALU_REMU;
            end

            default: begin
              // No match, keep decoder control signals IDLE
            end
          endcase
        end
      end // case: OPCODE_OP
      
      default: begin
        // No match, keep decoder control signals IDLE
      end
      
    endcase // unique case (instr_rdata_i[6:0])
    
  end // always_comb
  


endmodule : cv32e40x_m_decoder

