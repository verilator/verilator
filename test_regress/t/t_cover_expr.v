// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
    // Inputs
    clk
    );

    input clk;

    integer cyc;
    initial cyc=1;

    integer some_int;
    integer other_int;
    logic some_bool;

    wire t1 = cyc[0];
    wire t2 = cyc[1];
    wire t3 = cyc[2];
    wire t4 = cyc[3];

    localparam bit ONE = 1'b1;
    localparam bit ZERO = 1'b0;

    function automatic bit invert(bit x);
        return ~x;
    endfunction

    function automatic bit and_oper(bit a, bit b);
        return a & b;
    endfunction

    always @ (posedge clk) begin
        cyc <= cyc + 1;
        if ((~cyc[0] && cyc[1]) || (~cyc[2] && cyc[3])) $write("");
        if ((~t1 && t2) || (~t3 && t4)) $write("");
        if (t3 && (t1 == t2)) $write("");
        if (123 == (124 - 32'(t1 || t2))) $write("");
        some_int <= (t2 || t3) ? 345 : 567;
        some_bool <= t1 && t2;
        if (t1 & t2) $write("");
        if ((!t1 && t2) | (~t3 && t4)) $write("");
        if (t1 ^ t2) $write("");
        if (~(t1 & t2)) $write("");
        if (t1 -> t2) $write("");
        if (t1 <-> t2) $write("");
        if (&cyc[2:0]) $write("");
        if (&cyc[3:2]) $write("");
        if (|cyc[2:0]) $write("");
        if (^cyc[2:0]) $write("");
        if (|cyc[2:0] || cyc[3]) $write("");
        if (t1 & t2 & 1'b1) $write("");
        if (t1 & t2 & 1'b0) $write("");
        if (t1 & t2 & ONE) $write("");
        if (t1 & t2 & ZERO) $write("");
        if (t1 && t2) begin
            $write("");
        end else if (t1 || t2) begin
            $write("");
        end
        if (invert(t1) && t2) $write("");
        if (and_oper(t1, t2)) $write("");
        if (t2 && t3) begin
            if (t1 && t2) $write("");
        end
        if (0 == 1) begin
            for (int loop_var = 0; loop_var < 1; loop_var++) begin
                if (cyc[loop_var] && t2) $write("");
            end
        end
        // stop at the first layer even if there's more to find
        if ((cyc[3+32'(t1 && t2)+:2] == cyc[5+32'(t3 || t4)+:2]) || cyc[31]) $write("");
        // impossible branches and redundant terms
        if ((t1 && t2) && ~(t1 && t3) && (t1 || t4)) $write("");
        if ((cyc[0] && cyc[1]) && ~(cyc[0] && cyc[2]) && (cyc[0] || cyc[3])) $write("");
        // demonstrate current limitations of term matching scheme
        if ((cyc[0] && cyc[1]) && ~(cyc[1-1] && cyc[2]) && (cyc[2-2] || cyc[3])) $write("");
        //verilator coverage_off
        if (t1 && t2) $write("");
        //verilator coverage_on
        if ((~t1 && t2)
            ||
           (~t3 && t4)) $write("");
        // intentionally testing wonkified expression terms
        if (
            cyc[
              0
            ] &
            cyc
              [1]) $write("");
        // for now each ternary condition is considered in isolation
        other_int <= t1 ? t2 ? 1 : 2 : 3;
        // no expression coverage for multi-bit expressions
        if ((cyc[1:0] & cyc[3:2]) == 2'b11) $write("");
        // truth table is too large
        if (^cyc[6:0]) $write("");
        // this one is too big even for t_cover_expr_max
        if (^cyc) $write("");
        if (cyc==9) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end

    always_comb begin
        if (t1 && t2) $write("");
    end

    logic ta, tb, tc;
    initial begin
        int q[5];
        int qv;

        q = '{1, 2, 2, 4, 3};
        // lambas not handled
        // NB: there is a bug w/ tracing find_first (maybe lambdas in general?)
        //     tracing_off does not work around the bug
`ifndef TEST_TRACE
        qv = q.find_first with (item[0] & item[1]);
`endif
        ta = '1;
        tb = '0;
        tc = '0;
        while (ta || tb || tc) begin
            tc = tb;
            tb = ta;
            ta = '0;
        end
    end

    sub the_sub_1 (.p(t1), .q(t2));
    sub the_sub_2 (.p(t3), .q(t4));
    // TODO -- non-process expressions
    sub the_sub_3 (.p(t1 ? t2 : t3), .q(t4));

    // TODO
    // pragma for expr coverage off / on
    // investigate cover point sorting in annotated source
    // consider reporting don't care terms
    //
    // Branches which are statically impossible to reach are still reported.
    // E.g.
    // -000000  point: comment=(t1=1 && t2=1 && 1'h0=1) => 1 hier=top.t
    // These could potentially be pruned, but they currently follow suit for
    // what branch coverage does.  Perhaps a switch should be added to not
    // count statically impossible things.

endmodule

module sub (
    input p,
    input q
);

    always_comb begin
        if (p && q) $write("");
    end

endmodule
