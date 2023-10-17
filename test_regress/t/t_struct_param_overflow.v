// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Varun Koyyalagunta.
// SPDX-License-Identifier: CC0-1.0

package config_pkg;

    localparam int unsigned N = 10;

    typedef struct packed {
        logic [N-1:0][31:0] lo;
        logic [N-1:0][31:0] hi;
        logic [100-1:0][31:0] x;
        int unsigned n;
    } config_struct;

    function automatic logic subcheck(logic[31:0] lo, logic[31:0] hi, logic[31:0] val);
        return lo <= val && val < hi;
    endfunction

    function automatic logic check(config_struct cfg, logic[31:0] val);
        logic[N-1:0] good = '0;
        logic[N-1:0] bad  = '0;
        for (int i = 0; i < cfg.n; i++) begin
            good[i] = subcheck(cfg.lo[i], cfg.hi[i], val);
        end
        for (int i = cfg.n; i < N; i++) begin
            bad[i] = !(cfg.lo[i] == '0 && cfg.hi[i] == '0);
        end
        return good != '0 && bad == '0;
    endfunction

endpackage : config_pkg

module t(/*AUTOARG*/
    // Inputs
    clk
);

    input clk;
    import config_pkg::*;

    parameter config_struct MY_CONFIG = '{
        lo: {((N-3)*32)'('0), 32'h00, 32'h10, 32'h20},
        hi: {((N-3)*32)'('0), 32'h10, 32'h20, 32'h30},
        x : 3200'h0deadbeef,
        n : 3
    };

    struct_submodule #(.MY_CONFIG(MY_CONFIG)) a_submodule_I (.clk);
endmodule : t

module struct_submodule
    import config_pkg::*;
    #(
        parameter config_struct MY_CONFIG = '0
    ) (
        input clk
    );

    logic [31:0] val;
    logic c;
    int count = 0;

    assign val = 3;
    assign c   = check(MY_CONFIG, count);

    always @(posedge clk) begin
        count <= count + 1;
        if (c != '1) begin
            $error("c not 1");
            $stop;
        end
        if (count >= 10) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end

endmodule : struct_submodule
