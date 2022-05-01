// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t_embed1_wrap (/*AUTOARG*/
   // Outputs
   bit_out, vec_out, wide_out, did_init_out,
   // Inputs
   clk, bit_in, vec_in, wide_in, is_ref
   );

   /*AUTOINOUTMODULE("t_embed1_child")*/
   // Beginning of automatic in/out/inouts (from specific module)
   output bit           bit_out;
   output bit [30:0]    vec_out;
   output bit [123:0]   wide_out;
   output bit           did_init_out;
   input                clk;
   input                bit_in;
   input [30:0]         vec_in;
   input [123:0]        wide_in;
   input                is_ref;
   // End of automatics

`ifdef verilator
   // Import $t_embed_child__initial etc as a DPI function
`endif

   //TODO would like __'s as in {PREFIX}__initial but presently illegal for users to do this
   import "DPI-C" context function void t_embed_child_initial();
   import "DPI-C" context function void t_embed_child_final();
   import "DPI-C" context function void t_embed_child_eval();
   import "DPI-C" context function void t_embed_child_io_eval
     (
      //TODO we support bit, but not logic
      input bit clk,
      input bit bit_in,
      input bit [30:0] vec_in,
      input bit [123:0] wide_in,
      input bit is_ref,
      output bit bit_out,
      output bit [30:0] vec_out,
      output bit [123:0] wide_out,
      output bit did_init_out);

   initial begin
      // Load all values
      t_embed_child_initial();
   end

   // Only if system verilog, and if a "final" block in the code
   final begin
      t_embed_child_final();
   end

   bit _temp_bit_out;
   bit _temp_did_init_out;
   bit [30:0] _temp_vec_out;
   bit [123:0] _temp_wide_out;
   always @* begin
      t_embed_child_io_eval(
                            clk,
                            bit_in,
                            vec_in,
                            wide_in,
                            is_ref,
                            _temp_bit_out,
                            _temp_vec_out,
                            _temp_wide_out,
                            _temp_did_init_out
                            );
      // TODO might eliminate these temporaries
      bit_out = _temp_bit_out;
      did_init_out = _temp_did_init_out;
   end


   // Send all variables every cycle,
   // or have a sensitivity routine for each?
   //    How to make sure we call eval at end of variable changes?
   //      #0 (though not verilator compatible!)

   // TODO for now, we know what changes when
   always @ (posedge clk) begin
      vec_out <= _temp_vec_out;
      wide_out <= _temp_wide_out;
   end

endmodule
