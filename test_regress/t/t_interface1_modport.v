// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Very simple test for interface pathclearing

interface ifc;
  integer hidden_from_isub;
  integer value;
  modport out_modport (output value);
endinterface

module t (
   input clk
);

  integer cyc=1;

  ifc itop();

  sub  c1 (.isub(itop),
        .i_value(4));

  ifc iarr[1:0] ();
  ifc ione ();
  subarr c2 (.iarr(iarr), .ione(ione));

  always @ (posedge clk) begin
    cyc <= cyc + 1;
    if (cyc==20) begin
      if (itop.value != 4) $stop;
      itop.hidden_from_isub = 20;
      if (itop.hidden_from_isub != 20) $stop;
      if (iarr[0].value != 5) $stop;
      if (iarr[1].value != 6) $stop;
      if (ione.value != 7) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module sub
`ifdef NANSI  // bug868
  (
  isub, i_value
  );
  ifc.out_modport isub;   // Note parenthesis are not legal here
  input integer i_value;
`else
  (
  ifc.out_modport isub,
  input integer i_value
  );
`endif

  always @* begin
    isub.value = i_value;
  end
endmodule

module subarr
`ifdef NANSI
  (
  iarr, ione
  );
  ifc.out_modport iarr [1:0], ione;
`else
  (
  ifc.out_modport iarr [1:0], ione
  );
`endif

  // Slices of a modport array port
  leaf l0 (.ileaf(iarr[0:0]), .i_value(5));
  leaf l1 (.ileaf(iarr[1:1]), .i_value(6));
  assign ione.value = 7;
endmodule

module leaf (
  ifc.out_modport ileaf [0:0],
  input integer i_value
  );
  assign ileaf[0].value = i_value;
endmodule
