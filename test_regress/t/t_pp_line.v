// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

module t;
`line 100 "some file" 0
$info("aaaaaaaa file='%s'", `__FILE__);
$info("bbbbbbbb file='%s'", `__FILE__);
`line 200 "somefile.v" 0
$info("cccccccc file='%s'", `__FILE__);
`line 300 "/a/somefile.v" 0
$info("dddddddd file='%s'", `__FILE__);
`line 400 "C:\\a\\somefile.v" 0
$info("eeeeeeee file='%s'", `__FILE__);
endmodule
