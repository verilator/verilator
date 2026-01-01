// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

class func_c #(
    parameter p_width = 4
);
  static function logic [p_width-1:0] func(input logic [p_width-1:0] inb);
    func = inb;
  endfunction
endclass

module modA #(
    parameter p_width = 7
) (
    input logic [p_width-1:0] sig_a,
    output logic [p_width-1:0] sig_b
);
  assign sig_b = func_c#(p_width)::func(sig_a);
endmodule

module the_top ();
  localparam int Size = 3;

  logic [Size-1:0] sig_a;
  logic [Size-1:0] sig_b;
  logic [Size-1:0] sig_c;

  modA #(
      .p_width(Size)
  ) modA (
      .sig_a(sig_a),
      .sig_b(sig_b)
  );

  initial begin
    sig_a = 'h3;
    sig_c = func_c#(Size)::func('h5);
    #1;
    if (sig_b != 'h3) $stop;
    if (sig_c != 'h5) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
