// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );

   input in;  // inputs don't get flagged as undriven
   output out;  // outputs don't get flagged as unused

   sub sub ();

   // Check we don't warn about unused UDP signals
   udp_mux2 udpsub (out, in, in, in);

   // Check ignoreds mark as used
   reg 	  sysused;
   initial $bboxed(sysused);

   // Check file IO.  The fopen is the "driver" all else a usage.
   integer infile;
   integer outfile;
   initial begin
      outfile = $fopen("obj_dir/t_lint_unused_bad/open.log", "w");
      $fwrite(outfile, "1\n");
      $fclose(outfile);
      infile = $fopen("obj_dir/t_lint_unused_bad/open.log", "r");
      if ($fgetc(infile) != "1") begin end
   end

   wire   _unused_ok;

endmodule

module sub;

   wire pub /*verilator public*/;   // Ignore publics

   localparam THREE = 3;

endmodule

primitive udp_mux2 (q, a, b, s);
   output q;
   input  a, b, s;
   table
      //a b  s  :  out
      1   ?  0  :  1 ;
      0   ?  0  :  0 ;
      ?   1  1  :  1 ;
      ?   0  1  :  0 ;
      0   0  x  :  0 ;
      1   1  x  :  1 ;
   endtable
endprimitive
