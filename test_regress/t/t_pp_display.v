// $Id: t_delay.v 965 2007-10-31 20:29:07Z wsnyder $
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t;
   wire d1 = 1'b1;
   wire d2 = 1'b1;
   wire d3 = 1'b1;
   wire o1,o2,o3;
   add1 add1 (d1,o1);
   add2 add2 (d2,o2);

`define ls left_side
`define rs right_side
`define noarg  na//note extra space
`define thru(x) x
`define thruthru `ls `rs	// Doesn't expand
`define msg(x,y) `"x: `\`"y`\`"`"
   initial begin
      //$display(`msg( \`, \`));  // Illegal
      $display(`msg(pre `thru(thrupre `thru(thrumid) thrupost) post,right side));
      $display(`msg(left side,right side));
      $display(`msg( left side , right side ));
      $display(`msg( `ls , `rs ));
      $display(`msg( `noarg , `rs ));
      $display(`msg( prep ( midp1 `ls midp2 ( outp ) ) , `rs ));
      $display(`msg(`noarg,`noarg`noarg));
      $display(`msg( `thruthru , `thruthru ));   // Results vary between simulators
      $display(`msg(`thru(),));  // Empty
      $display(`msg(`thru(left side),`thru(right side)));
      $display(`msg( `thru( left side ) , `thru( right side ) ));

`define twoline first \
 second
      $display(`msg(twoline, `twoline));

      //$display(`msg(left side, \ right side \ ));  // Not sure \{space} is legal.
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

`define ADD_UP(a,c)          \
wire  tmp_``a = a; \
wire  tmp_``c = tmp_``a + 1; \
assign c = tmp_``c ;

module add1 ( input wire d1, output wire o1);
 `ADD_UP(d1,o1)   // expansion is OK
endmodule
module add2 ( input wire d2, output wire o2);
 `ADD_UP( d2 , o2 )  // expansion is bad
endmodule
// `ADD_UP( \d3 , \o3 )  // This really is illegal
