// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Verilator Authors.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define checkd(got, expected) \
  if ((got) != (expected)) $stop

typedef struct {
  rand int value;
} Entry;

class Collection;
  rand Entry entries[];

  constraint c_size {
    entries.size() == 3;
  }

  constraint c_values {
    foreach (entries[i]) {
      entries[i].value[3:0] dist {
        0      :/ 0,
        [1:15] :/ 1
      };
    }
  }
endclass

module t;
  initial begin
    automatic int randomize_result;

    repeat (20) begin
      automatic Collection object = new;
      object.entries.rand_mode(0);
      object.entries = new[3];
      object.entries[0].value = 1;
      object.entries[1].value = 2;
      object.entries[2].value = 15;
      randomize_result = object.randomize();
      `checkd(randomize_result, 1);
      `checkd(object.entries.size(), 3);
      `checkd(object.entries[0].value, 1);
      `checkd(object.entries[1].value, 2);
      `checkd(object.entries[2].value, 15);

      object.entries.rand_mode(1);
      randomize_result = object.randomize();
      `checkd(randomize_result, 1);
      `checkd(object.entries.size(), 3);
      foreach (object.entries[i]) begin
        `checkd(object.entries[i].value[3:0] != 0, 1);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
