// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input string empty_no_opt
);
  initial begin
    automatic string format;
    automatic string s;

    format = "got=%0d rest b=%b c=%c d=%d e=%e f=%f g=%g h=%h o=%o p=%p s=%s t=%t u=%u v=%v z=%z";
    $sformat(s, {format, empty_no_opt}, 42);
    $display("%s", s);

    format = "got=%0D rest B=%B C=%C D=%D E=%E F=%F G=%G H=%H O=%O P=%P S=%S T=%T U=%U V=%V Z=%Z";
    $sformat(s, {format, empty_no_opt}, 42);
    $display("%s", s);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
