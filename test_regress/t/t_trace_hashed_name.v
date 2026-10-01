// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

// Every name here is over the 128 character limit at which VName hashes it, so the
// passes that append to a name append to a hash: V3SplitVar a bit range or an element
// index, V3Class a package suffix.

class class_with_a_name_long_enough_that_verilator_replaces_it_with_a_hash_because_it_is_over_the_one_hundred_twenty_eight_character_limit;
  int x;
endclass

module t;
  logic [1:0] packed_signal_with_a_name_long_enough_that_verilator_replaces_it_with_a_hash_because_it_is_over_the_one_hundred_twenty_eight_char_limit /*verilator split_var*/;
  logic unpacked_array_with_a_name_long_enough_that_verilator_replaces_it_with_a_hash_because_it_is_over_the_one_hundred_twenty_eight_char_limit [1:0] /*verilator split_var*/;
  class_with_a_name_long_enough_that_verilator_replaces_it_with_a_hash_because_it_is_over_the_one_hundred_twenty_eight_character_limit obj;

  always_comb packed_signal_with_a_name_long_enough_that_verilator_replaces_it_with_a_hash_because_it_is_over_the_one_hundred_twenty_eight_char_limit[0] = 1'b1;
  always_comb unpacked_array_with_a_name_long_enough_that_verilator_replaces_it_with_a_hash_because_it_is_over_the_one_hundred_twenty_eight_char_limit[0] = 1'b1;

  initial begin
    obj = new;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
