// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module dpi_test ();

reg rtl_clk;
initial begin
    rtl_clk = 1'b0;
    forever
        #2 rtl_clk = ~rtl_clk;
end

    export "DPI-C" v_export = task dpi_export;
    task dpi_export(input int unsigned i);
        @(posedge rtl_clk); // comment this out for the task to be executed
        $display("%t: v_export: i=%3d", $time, i);
    endtask

    import "DPI-C" context task dpi_import(input int unsigned n);

    integer n;
initial begin
        $display("Dumping waveforms");
        $dumpfile("waves.fst");
        for (n = 3; n < 6; n = n + 1) begin
            $display("%t: calling dpi_import: n =%3d", $time, n);
            dpi_import(n);
        end
        $finish;
end
endmodule
