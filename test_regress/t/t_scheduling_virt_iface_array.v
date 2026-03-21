// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test: Class member is an array of virtual interfaces.
// The conditional trigger must handle VIF accesses through array
// elements correctly.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface SimpleIf;
  logic [7:0] data;
endinterface

class VifHolder;
  virtual SimpleIf vifs[2];

  function new(virtual SimpleIf a, virtual SimpleIf b);
    vifs[0] = a;
    vifs[1] = b;
  endfunction
endclass

module t;
  logic clk = 0;
  int cyc = 0;

  SimpleIf intf0();
  SimpleIf intf1();

  virtual SimpleIf vi0 = intf0;
  virtual SimpleIf vi1 = intf1;

  VifHolder holder = new(intf0, intf1);

  // Write through virtual interface handles
  always @(posedge clk) begin
    if (cyc == 1) vi0.data <= 8'hAA;
    if (cyc == 2) vi1.data <= 8'hBB;
    if (cyc == 3) vi0.data <= 8'hCC;
    if (cyc == 4) vi1.data <= 8'hDD;
  end

  // Read through array-of-VIF class member
  logic [7:0] obs0, obs1;
  assign obs0 = holder.vifs[0].data;
  assign obs1 = holder.vifs[1].data;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      2: if (obs0 != 8'hAA) $stop;
      3: if (obs1 != 8'hBB) $stop;
      4: if (obs0 != 8'hCC) $stop;
      5: if (obs1 != 8'hDD) $stop;
      6: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase
  end

  initial begin
    repeat (20) #5 clk = ~clk;
  end
endmodule
