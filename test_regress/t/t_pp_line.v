// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

module t;
`line 100 "some file" 0
$info("aaaaaaaa");
$info("bbbbbbbb");
`line 200 "somefile.v" 0
$info("cccccccc");
`line 300 "/a/somefile.v" 0
$info("dddddddd");
endmodule
