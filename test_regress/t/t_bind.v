// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

bit a_finished;
bit b_finished;
bit lib_bound;

module t (
    input clk
);

  wire [31:0] o;
  wire si = 1'b0;

  ExampInst i (  // Outputs
      .o(o[31:0]),
      // Inputs
      .i(1'b0)
  /*AUTOINST*/);

  LibraryModule library_inst ();
  LibraryBound unused_bound ();

  Prog p (  /*AUTOINST*/
      // Inputs
      .si(si)
  );

  always @(posedge clk) begin
    if (!a_finished) $stop;
    if (!b_finished) $stop;
`ifdef VERILATOR
    // The bind should not apply to the module marked 'verilator_lib'
    if (lib_bound) $stop;
`endif
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module InstModule (
    output logic [31:0] so,
    input si
);
  assign so = {32{si}};
endmodule

module LibraryModule;
endmodule
`ifdef VERILATOR
`verilator_config
verilator_lib -module "LibraryModule"
`verilog
`endif

module LibraryBound #(
    parameter bit ENABLE = 1'b0
);
  initial lib_bound = ENABLE;
endmodule

bind LibraryModule LibraryBound #(.ENABLE(1'b1)) bound_instance ();

program Prog (
    input si
);
  initial a_finished = 1'b1;
endprogram

module ExampInst (
    o,
    i
);
  output logic [31:0] o;
  input i;

  InstModule instName (  // Outputs
      .so(o[31:0]),
      // Inputs
      .si(i)
  /*AUTOINST*/);

  //bind InstModule Prog instProg
  //    (.si(si));

  // Note is based on context of caller
  bind InstModule Prog instProg (  /*AUTOBIND*/
      .si(si)
  );

endmodule

// Check bind at top level
bind InstModule Prog2 instProg2 (  /*AUTOBIND*/
    .si(si)
);

// Check program declared after bind
program Prog2 (
    input si
);
  initial b_finished = 1'b1;
endprogram
