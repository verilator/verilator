// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [83:4] 		from;
   reg [83:4] 		to;
   reg [6:0] 		bitn;
   reg [3:0] 		nibblep;
   reg [3:0] 		nibblem;

   reg [7:0] cyc; initial cyc=0;

   always @* begin
      nibblep = from[bitn +: 4];
      nibblem = from[bitn -: 4];
      to = from;
      to[bitn +: 4] = cyc[3:0];
      to[bitn -: 4] = cyc[3:0];
   end

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%d nibblep==%b nibblem==%b to^from==%x\n",$time, cyc, nibblep, nibblem, from^to);
      cyc <= cyc + 8'd1;
      case (cyc)
	8'd00: begin from<=80'h7bea9d779b67e48f67da; bitn<=7'd7; end
	8'd01: begin from<=80'hefddce326b11ca5dc448; bitn<=7'd8; end
	8'd02: begin from<=80'h3f99c5f34168401e210d; bitn<=7'd4; end  // truncate -:
	8'd03: begin from<=80'hc90635f0a7757614ce3f; bitn<=7'd79; end
	8'd04: begin from<=80'hc761feca3820331370ec; bitn<=7'd83; end // truncate +:
	8'd05: begin from<=80'hd6e36077bf28244f84b5; bitn<=7'd6; end  // half trunc
	8'd06: begin from<=80'h90118c5d3d285a1f3252; bitn<=7'd81; end // half trunc
	8'd07: begin from<=80'h38305da3d46b5859fe16; bitn<=7'd67; end
	8'd08: begin from<=80'h4b9ade23a8f5cc5b3111; bitn<=7'd127; end // truncate
	8'd09: begin
	   $write("*-* All Finished *-*\n");
	   $finish;
	end
	default: ;
      endcase
      case (cyc)
	8'd00: ;
	8'd01: begin if ((nibblep & 4'b1111)!==4'b1011) $stop; if ((nibblem & 4'b1111)!==4'b1010) $stop; end
	8'd02: begin if ((nibblep & 4'b1111)!==4'b0100) $stop; if ((nibblem & 4'b1111)!==4'b0100) $stop; end
	8'd03: begin if ((nibblep & 4'b1111)!==4'b1101) $stop; if ((nibblem & 4'b0000)!==4'b0000) $stop; end
	8'd04: begin if ((nibblep & 4'b1111)!==4'b1001) $stop; if ((nibblem & 4'b1111)!==4'b1001) $stop; end
	8'd05: begin if ((nibblep & 4'b0000)!==4'b0000) $stop; if ((nibblem & 4'b1111)!==4'b1100) $stop; end
	8'd06: begin if ((nibblep & 4'b1111)!==4'b1101) $stop; if ((nibblem & 4'b0000)!==4'b0000) $stop; end
	8'd07: begin if ((nibblep & 4'b0000)!==4'b0000) $stop; if ((nibblem & 4'b1111)!==4'b0100) $stop; end
	8'd08: begin if ((nibblep & 4'b1111)!==4'b0000) $stop; if ((nibblem & 4'b1111)!==4'b0101) $stop; end
	8'd09: begin if ((nibblep & 4'b0000)!==4'b0000) $stop; if ((nibblem & 4'b0000)!==4'b0000) $stop; end
	default: $stop;
      endcase
      case (cyc)
	8'd00: ;
	8'd01: begin if ((to^from)!==80'h0000000000000000005b) $stop; end
	8'd02: begin if ((to^from)!==80'h0000000000000000006c) $stop; end
	8'd03: begin if ((to^from)!==80'h0000000000000000000e) $stop; end
	8'd04: begin if ((to^from)!==80'h6d000000000000000000) $stop; end
	8'd05: begin if (((to^from)&~80'hf)!==80'h90000000000000000000) $stop; end  // Exceed bounds, verilator may write index 0
	8'd06: begin if (((to^from)&~80'hf)!==80'h00000000000000000020) $stop; end  // Exceed bounds, verilator may write index 0
	8'd07: begin if (((to^from)&~80'hf)!==80'h4c000000000000000000) $stop; end
	8'd08: begin if ((to^from)!==80'h0004d000000000000000) $stop; end
	8'd09: begin if (((to^from)&~80'hf)!==80'h00000000000000000000) $stop; end
	default: $stop;
      endcase
   end

endmodule
