// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Alex Solomatnikov.
// SPDX-License-Identifier: CC0-1.0

package z_pkg;
   localparam int OPCODEW=3;
   localparam int CIDW=4;
   localparam int SIDW=10;
   localparam int CTAGW=7;
   localparam int STAGW=9;
   localparam int STATEW=3;
   localparam int ADDRW=37;
   localparam int DATAW=256;
   localparam int MASKW=DATAW/8;
   localparam int SIZEW=4;
   typedef enum   logic [OPCODEW-1:0] {
				       A   = 3'h 0,
				       B   = 3'h 1
				       } a_op_t;
   typedef enum   logic [OPCODEW-1:0] {
				       C   = 3'h 0,
				       D   = 3'h 1
				       } b_op_t;
   typedef enum   logic [OPCODEW-1:0] {
				       E   = 3'h 0,
				       F   = 3'h 1
				       } c_op_t;
   typedef enum   logic [OPCODEW-1:0] {
				       G       = 3'h 0,
				       H       = 3'h 1
				       } d_op_t;
   typedef logic [CIDW-1:0] cid_t;
   typedef logic [SIDW-1:0] sid_t;
   typedef logic [CTAGW-1:0] ctag_t;
   typedef logic [STAGW-1:0] stag_t;
   typedef logic [STATEW-1:0] state_t;
   typedef logic [ADDRW-1:0]  address_t;
   typedef logic [SIZEW-1:0]  size_t;
   typedef logic [DATAW-1:0]  data_t;
   typedef logic [MASKW-1:0]  mask_t;
   typedef struct 	      packed {
      cid_t        cid;
      a_op_t       opcode;
      address_t    address;
   } x1_ch_t;
   typedef struct 	      packed {
      cid_t        cid;
      b_op_t      opcode;
      address_t    address;
   } x2_ch_t;
   typedef struct 	      packed {
      cid_t        cid;
      sid_t        sid;
      ctag_t       ctag;
      stag_t       stag;
      c_op_t      opcode;
      state_t   state2;
      state_t   state3;
      address_t    address;
      logic 		      f4;
      size_t       size;
      logic 		      f2;
   } x3_ch_t;
   typedef struct 	      packed {
      cid_t        cid;
      sid_t        sid;
      ctag_t       ctag;
      stag_t       stag;
      d_op_t       opcode;
      state_t   state1;
      logic 		      f4;
      logic 		      f1;
      size_t       size;
      logic 		      f3;
   } x4_ch_t;
   typedef struct 	      packed {
      cid_t        cid;
      ctag_t       ctag;
      stag_t       stag;
      d_op_t       opcode;
      logic 		      f1;
      logic 		      f3;
   } x5_ch_t;
   typedef struct 	      packed {
      logic 		      last;
      logic 		      corrupt;
   } x6_ch_t;
   typedef struct 	      packed {
      sid_t        sid;
      stag_t       stag;
   } x7_ch_t;
   typedef enum 	      {
			       CH_X1,
			       CH_Y1,
			       CH_Y2,
			       CH_X2,
			       CH_X3,
			       CH_Y3,
			       CH_X4,
			       CH_X5,
			       CH_X6,
			       CH_X7
			       } channel_t;
   parameter channel_t CH_ALL[CH_X7+1] = '{CH_X1, CH_Y1, CH_Y2, CH_X2, CH_X3, CH_Y3, CH_X4, CH_X5, CH_X6, CH_X7};
   typedef enum 	      {
			       TXN_0,
			       TXN_1,
			       TXN_2,
			       TXN_3,
			       TXN_4,
			       TXN_5,
			       TXN_6,
			       TXN_7
			       } txn_type_t;
   function txn_type_t txn_type(bit [2:0] opcode, channel_t ch);
      case(opcode)
        3'd0: begin
           case(ch)
             CH_X1: txn_type = TXN_1;
             CH_X2: txn_type = TXN_7;
             CH_X3: txn_type = TXN_7;
             CH_Y3: txn_type = TXN_7;
             CH_X4: txn_type = TXN_2;
             CH_X6: txn_type = TXN_2;
             default:   txn_type = TXN_0;
           endcase
        end
        3'd1: begin
           case(ch)
             CH_Y1: txn_type = TXN_3;
             CH_X2: txn_type = TXN_4;
             CH_X3: txn_type = TXN_5;
             CH_Y3: txn_type = TXN_5;
             CH_X5: txn_type = TXN_6;
             default:   txn_type = TXN_0;
           endcase
        end
        3'd2: begin
           case(ch)
             CH_Y1: txn_type = TXN_7;
             CH_X2: txn_type = TXN_7;
             CH_X3: txn_type = TXN_7;
             CH_Y3: txn_type = TXN_7;
             CH_X4: txn_type = TXN_7;
             CH_X6: txn_type = TXN_7;
             default:   txn_type = TXN_0;
           endcase
        end
        3'd3: begin
           case(ch)
             CH_Y1: txn_type = TXN_7;
             CH_X2: txn_type = TXN_7;
             CH_X3: txn_type = TXN_7;
             CH_Y3: txn_type = TXN_7;
             CH_X5: txn_type = TXN_7;
             default:   txn_type = TXN_0;
           endcase
        end
        3'd4: begin
           case(ch)
             CH_X1: txn_type = TXN_7;
             CH_X2: txn_type = TXN_7;
             CH_X3: txn_type = TXN_7;
             CH_Y3: txn_type = TXN_7;
             CH_X4: txn_type = TXN_7;
             CH_X6: txn_type = TXN_7;
             CH_X7: txn_type = TXN_7;
             default:   txn_type = TXN_0;
           endcase
        end
        3'd5: begin
           case(ch)
             CH_Y1: txn_type = TXN_7;
             CH_X2: txn_type = TXN_7;
             CH_X3: txn_type = TXN_7;
             CH_Y3: txn_type = TXN_7;
             CH_X5: txn_type = TXN_7;
             default:   txn_type = TXN_0;
           endcase
        end
        3'd6: begin
           case(ch)
             CH_X3: txn_type = TXN_7;
             CH_Y3: txn_type = TXN_7;
             CH_X5: txn_type = TXN_7;
             default: txn_type = TXN_0;
           endcase
        end
        3'd7: begin
           case(ch)
             CH_Y2: txn_type = TXN_7;
             default: txn_type = TXN_0;
           endcase
        end
      endcase
   endfunction
endpackage
interface z_if;
   import z_pkg::*;
   logic         x1_valid;
   x1_ch_t       x1;
   logic         x2_valid;
   x2_ch_t       x2;
   logic         x3_valid;
   x3_ch_t       x3;
   logic         x4_valid;
   x4_ch_t       x4;
   logic         x5_valid;
   x5_ch_t       x5;
   logic         x6_valid;
   x6_ch_t       x6;
   data_t        x6_data;
   logic         x7_valid;
   x7_ch_t       x7;
   function automatic logic x2_trig(); return x2_valid; endfunction
   function automatic logic x4_trig(); return x4_valid; endfunction
   function automatic logic x5_trig(); return x5_valid; endfunction
   function automatic logic x6_trig(); return x6_valid; endfunction
   modport sender (
		   output x1_valid,
		   output x1,
		   input  x2_valid,
		   input  x2,
		   output x3_valid,
		   output x3,
		   input  x4_valid,
		   input  x4,
		   input  x5_valid,
		   input  x5,
		   input  x6_valid,
		   input  x6,
		   input  x6_data,
		   output x7_valid,
		   output x7,
		   import x2_trig,
		   import x4_trig,
		   import x5_trig,
		   import x6_trig
		   );
   modport receiver (
		     input  x1_valid,
		     input  x1,
		     output x2_valid,
		     output x2,
		     input  x3_valid,
		     input  x3,
		     output x4_valid,
		     output x4,
		     output x5_valid,
		     output x5,
		     output x6_valid,
		     output x6,
		     output x6_data,
		     input  x7_valid,
		     input  x7,
		     import x2_trig,
		     import x4_trig,
		     import x5_trig,
		     import x6_trig
		     );
endinterface
class z_txn_class;
   import z_pkg::*;
   rand txn_type_t   req_txn_type;
   rand cid_t        cid;
   rand sid_t        sid;
   rand ctag_t       ctag;
   rand stag_t       stag;
   rand size_t       size;
   rand address_t    address;
   rand state_t   state1;
   rand state_t   state2;
   rand state_t   state3;
   rand logic 		    f1;
   rand logic 		    f2;
   rand logic 		    f3;
   rand logic 		    f4;
   data_t            data[];
   mask_t            mask[];
   bit 			    corrupt[];
   logic [2:0] 		    req_opcode;
endclass
module z_bfm_sender import z_pkg::*;
   (
    input logic clk,
    input logic reset_l,
    z_if.sender z_if_sender
    );
   channel_t ch;
   typedef z_txn_class z_txn_q_t[$];
   z_txn_q_t z_txn_qs[ch.num()];
   z_txn_class z_txn[ch.num()];
   always @(posedge clk or negedge reset_l) begin
      if (!reset_l) begin
	 z_if_sender.x1_valid <= '0;
	 z_if_sender.x3_valid <= '0;
	 z_if_sender.x7_valid <= '0;
      end
      else begin
	 foreach (CH_ALL[i]) begin
	    case(CH_ALL[i])
              CH_X1: begin
		 if (z_txn_qs[i].size() > 0) begin
		    z_txn[i] = z_txn_qs[i].pop_front();
		    z_if_sender.x1_valid     <= '1;
		    z_if_sender.x1.cid       <= z_txn[i].cid;
		    z_if_sender.x1.opcode    <= a_op_t'(z_txn[i].req_opcode);
		    z_if_sender.x1.address   <= z_txn[i].address;
		 end
	      end
              CH_X3: begin
		 if (z_txn_qs[i].size() > 0) begin
		    z_txn[i] = z_txn_qs[i].pop_front();
		    z_if_sender.x3_valid     <= '1;
		    z_if_sender.x3.cid       <= z_txn[i].cid;
		    z_if_sender.x3.sid       <= z_txn[i].sid;
		    z_if_sender.x3.ctag      <= z_txn[i].ctag;
		    z_if_sender.x3.stag      <= z_txn[i].stag;
		    z_if_sender.x3.opcode    <= c_op_t'(z_txn[i].req_opcode);
		    z_if_sender.x3.state2    <= z_txn[i].state2;
		    z_if_sender.x3.state3    <= z_txn[i].state3;
		    z_if_sender.x3.address   <= z_txn[i].address;
		    z_if_sender.x3.f4       <= z_txn[i].f4;
		    z_if_sender.x3.size      <= z_txn[i].size;
		    z_if_sender.x3.f2     <= z_txn[i].f2;
		 end
	      end
              CH_X7: begin
		 if (z_txn_qs[i].size() > 0) begin
		    z_txn[i] = z_txn_qs[i].pop_front();
		    z_if_sender.x7.sid       <= z_txn[i].sid;
		    z_if_sender.x7.stag      <= z_txn[i].stag;
		 end
	      end
              CH_X2: begin
		 if (z_if_sender.x2_trig()) begin
		    z_txn[i] = new;
		    z_txn[i].req_txn_type = txn_type(z_if_sender.x2.opcode, ch);
		    z_txn[i].cid          = z_if_sender.x2.cid;
		    z_txn[i].address      = z_if_sender.x2.address;
		    z_txn_qs[i].push_back(z_txn[i]);
		 end
	      end
              CH_X4: begin
		 if (z_if_sender.x4_trig()) begin
		    z_txn[i] = new;
		    z_txn[i].req_txn_type = txn_type(z_if_sender.x4.opcode, ch);
		    z_txn[i].cid          = z_if_sender.x4.cid;
		    z_txn[i].sid          = z_if_sender.x4.sid;
		    z_txn[i].ctag         = z_if_sender.x4.ctag;
		    z_txn[i].stag         = z_if_sender.x4.stag;
		    z_txn[i].state1       = z_if_sender.x4.state1;
		    z_txn[i].f1       = z_if_sender.x4.f1;
		    z_txn[i].f4          = z_if_sender.x4.f4;
		    z_txn[i].size         = z_if_sender.x4.size;
		    z_txn[i].f3      = z_if_sender.x4.f3;
		    z_txn_qs[i].push_back(z_txn[i]);
		 end
	      end
              CH_X5: begin
		 if (z_if_sender.x5_trig()) begin
		    z_txn[i] = new;
		    z_txn[i].req_txn_type = txn_type(z_if_sender.x5.opcode, ch);
		    z_txn[i].cid          = z_if_sender.x5.cid;
		    z_txn[i].ctag         = z_if_sender.x5.ctag;
		    z_txn[i].f1       = z_if_sender.x5.f1;
		    z_txn_qs[i].push_back(z_txn[i]);
		 end
              end
              CH_X6: begin
		 if (z_if_sender.x6_trig()) begin
		    z_txn[i] = new;
		    z_txn[i].data         = new[1];
		    z_txn[i].corrupt      = new[1];
		    z_txn[i].data[0]      = z_if_sender.x6_data;
		    z_txn[i].corrupt[0]   = z_if_sender.x6.corrupt;
		    z_txn_qs[i].push_back(z_txn[i]);
		 end
	      end
	    endcase
	 end
      end
   end
endmodule
module test_core_wrapper
  (
   input logic clk,
   input logic reset_l,
   z_if.sender z,
   mmio_z
   );
   z_bfm_sender mem_z_bfm( .z_if_sender(z),
			   .*);
   z_bfm_sender mmio_z_bfm( .z_if_sender(mmio_z),
		   	    .*);
endmodule
module t
  (
   input clk,
   input reset_l
   );
   z_if         z(),
     mmio_z();
   test_core_wrapper tile( .z     (z.sender),
			   .mmio_z(mmio_z.sender),
			   .*);
endmodule
