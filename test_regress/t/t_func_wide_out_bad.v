// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   parameter MSG_PORT_WIDTH = 4350;
   localparam PAYLOAD_MAX_BITS = 4352;

   reg [MSG_PORT_WIDTH-1:0] msg;

   initial begin
      // Operator TASKREF 'func' expects 4352 bits on the Function Argument, but Function Argument's VARREF 'msg' generates 4350 bits.
      // verilator lint_off WIDTH
      func(msg);
      // verilator lint_on WIDTH
      if (msg !== {MSG_PORT_WIDTH{1'b1}}) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   function integer func (output bit [PAYLOAD_MAX_BITS-1:0] data);
      /*verilator no_inline_task*/
      data = {PAYLOAD_MAX_BITS{1'b1}};
      return 1;
   endfunction

endmodule
