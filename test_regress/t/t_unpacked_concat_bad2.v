// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: CC0-1.0

module t;

  logic [7:0] s0;
  logic [7:0] s1[1:2];
  logic [7:0] s2[1:4];
  logic [7:0] s3[2][2];

  typedef int AI3[1:3];
  AI3 A3;
  logic [31:0] A9_logic[1:9];

  initial begin
    // RHS has too many elements.
    s1 = {s0, s2};
    s2 = {s1, s0, s0, s0};
    // Incompatible type
    s2 = {s0, s3};

    A9_logic = {A3, 4, 5, A3, 6};
    $write("*-* All Finished *-*\n");
    $finish;
  end

  class Cls;
  endclass
  class Other;
  endclass

  initial begin
    Cls cq[$];
    Cls cd[];
    Other o;
    // Item of an incompatible type, so neither an element nor an array
    cq = {cq, o};
    cd = {o, cd};
    cq = '{o};
  end

  initial begin
    Cls cq[$];
    Other oq[$];
    Other od[];
    Other ou[2];
    Other ob[$:2];
    // Array of an incompatible type, so not an array of elements
    cq = {cq, oq};
    cq = {od, cq};
    cq = {cq, ou};
    cq = {cq, ob};
  end

  initial begin
    Cls c;
    Cls cq[$];
    int iq[$];
    int id[];
    // Class handle and integral items or arrays, so neither an element nor an array of them
    iq = {iq, c};
    id = {c, id};
    iq = '{c};
    cq = {cq, 5};
    iq = {iq, cq};
    cq = {cq, iq};
  end

  typedef Cls cls_t;
  typedef Other oq_t[$];

  initial begin
    cls_t tq[$];
    oq_t oq;
    Other o;
    // Typedef'd element and array types
    tq = {tq, o};
    tq = {tq, oq};
  end

  initial begin
    Cls c;
    int iq[$];
    int qq[$][$];
    Cls cqq[$][$];
    // Element type that is itself an unpacked array
    qq = {qq, c};
    qq = '{c};
    cqq = {cqq, iq};
  end
endmodule
