// DESCRIPTION: Verilator: Finish effects from default arguments
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

class defaults_c;
  static bit gate = 1;

  static function automatic int finishing_default();
    $finish;
    return 13;
  endfunction
endclass

module t;
  int explicit_after;
  int omitted_after;
  int outer_after;

  task automatic consume(
      input bit value = (defaults_c::finishing_default() != 0) && defaults_c::gate);
    if (value == -1) $stop;
  endtask

  task automatic explicit_path;
    consume(1);
    ++explicit_after;
  endtask

  task automatic omitted_path;
    consume();
    ++omitted_after;
  endtask

  initial begin
    explicit_path();
    if (explicit_after != 1) $stop;
    omitted_path();
    ++outer_after;
  end

  final begin
    if (explicit_after != 1) $stop;
    if (omitted_after != 0) $stop;
    if (outer_after != 0) $stop;
    $write("*-* All Finished *-*\n");
  end
endmodule
