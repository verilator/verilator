// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class base #(
    type T = int
);
endclass

class missing_type extends base #(int);
  missing_t value;
endclass

interface class interface_base #(
    type T = int
);
endclass

virtual class implemented_type implements interface_base #(int);
  T value;
endclass

class nonclass_base #(
    type B = int
) extends B;
  missing_t value;
endclass

class cycle_a #(
    int N = 1
) extends cycle_b #(N);
  missing_t value;
endclass

class cycle_b #(
    int N = 1
) extends cycle_a #(N);
endclass

// A name qualified by the class itself is searched in the specialization and its bases
class self_missing #(
    type T = int
);
  self_missing::missing_t value;
endclass

module t;
  missing_type missing;
  implemented_type implemented;
  nonclass_base #() nonclass;
  cycle_a #(2) cycle;
  self_missing #(byte) self_miss;
endmodule
