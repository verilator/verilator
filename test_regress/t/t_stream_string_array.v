// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
   string qs[$];
   string as[];
   string s;
   initial begin
      s = {>>{qs}};
      if (s != "") $stop;

      s = {>>{as}};
      if (s != "") $stop;

      qs = '{"ab", "c", ""};
      s = {>>{qs}};
      if (s != "abc") $stop;

      as = new[3];
      as[0] = "abcd";
      as[2] = "ef";
      s = {>>{as}};
      if (s != "abcdef") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
