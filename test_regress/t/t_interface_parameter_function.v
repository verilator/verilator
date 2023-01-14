// DESCRIPTION: Verilator: Verilog Test module
//
// Following code should not throw any internal error.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Gökçe Aydos.
// SPDX-License-Identifier: CC0-1.0

interface intf #(A=0);
	typedef logic logic_t;
	
	function logic_t f();
		return 0;
	endfunction
	
	modport if_m (
		import f
	);
endinterface

module t;
	intf #(1) intf1();
	m m0(.*);
endmodule

module m (intf.if_m intf1);
	if (intf1.f())
		$error();

	initial begin
		$write("*-* All Finished *-*\n");
		$finish;
	end
endmodule
