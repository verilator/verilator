// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

typedef logic [6:0] row_t[3:2];

typedef struct {
  logic [6:0] x;
  row_t sa;
} st_t;

interface Ifc;
  logic [6:0] sig;
  row_t arr;
  st_t st;
  modport mp(output sig);
endinterface

typedef virtual Ifc vif_t;

module t;
  Ifc ifc ();
  logic [6:0] v;

  // Variables of an interface instance
  initial begin
    force ifc.sig = 7'h55;  // OK
    force ifc.arr[2] = 7'h55;  // OK
    release ifc.sig;  // OK
  end

  // Variables selected through a virtual interface
  virtual Ifc vif = ifc;
  initial begin
    force vif.sig = 7'h55;  // Unsupported
    force vif.sig[3:1] = 3'h5;  // Unsupported
    force vif.arr[2] = 7'h55;  // Unsupported
    force vif.arr = ifc.arr;  // Unsupported
    force vif.st.x = 7'h55;  // Unsupported
    force vif.st.sa[3] = 7'h55;  // Unsupported
    force {v, vif.sig} = 14'h1234;  // Unsupported
    release vif.sig;  // Unsupported
    release vif.arr[2];  // Unsupported
  end

  // Also with a type definition, a modport, or as an element of an array
  vif_t vt = ifc;
  virtual Ifc.mp vmp = ifc;
  virtual Ifc vifs[2:1];
  initial begin
    force vt.sig = 7'h55;  // Unsupported
    force vmp.sig = 7'h55;  // Unsupported
    force vifs[1].sig = 7'h55;  // Unsupported
  end

  // Also in a procedural continuous assignment
  initial begin
    // verilator lint_off IEEEMAYDEPRECATE
    assign vif.sig = 7'h55;  // Unsupported
    assign vif.arr[2] = 7'h55;  // Unsupported
    deassign vif.sig;  // Unsupported
    deassign vif.arr[2];  // Unsupported
    // verilator lint_on IEEEMAYDEPRECATE
  end

  // Other assignments may write through a virtual interface, and anything may read
  initial begin
    vif.sig = 7'h11;  // OK
    vif.arr[2] <= 7'h12;  // OK
    force v = vif.sig;  // OK
  end
endmodule
