// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

class func_c #(
    parameter p_width = 4
);
  typedef struct packed {logic [p_width-1:0] data;} my_type_t;
  static function my_type_t func(input logic [p_width-1:0] inb);
    func.data = inb;
  endfunction
endclass

module modA #(
    parameter p_width = 7
) (
    input func_c#(p_width)::my_type_t sig_a,
    output func_c#(p_width)::my_type_t sig_b
);
  assign sig_b.data = func_c#(p_width)::func(sig_a);
endmodule

module the_top ();
  localparam int Size = 3;

  func_c #(Size)::my_type_t sig_a, sig_b, sig_c;

  modA #(
      .p_width(Size)
  ) modA (
      .sig_a(sig_a),
      .sig_b(sig_b)
  );

  initial begin
    sig_a.data = 'h3;
    sig_c.data = func_c#(Size)::func('h5);
    #1;
    if (sig_b.data != 'h3) $stop;
    if (sig_c.data != 'h5) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
