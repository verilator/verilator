// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
    clk
    );
    input clk;
    string str1, str2, str3;
    reg [127:0] a;
    reg [31:0] b;
    reg [80:0] c;
    reg [80:0] d;
    reg [80:0] tmp;
    integer cyc; initial cyc = 1;
    initial
        begin
            a = 128'h2a1261617221212130031;
            b = 32'b110000000011111111;
            c = 81'hfffffffffffffffffffff;
            d = 81'hfffffffffffffffffffff;
            str1 = a;
            str2 = b;
            $display("********************************************");
            $display("init bin val %b, str val %b", a, str1);
            $display("init hex val %h, str val %h", a, str1);
            $display("init dec val %d, str val %d", a, str1);
            $display("init oct val %o, str val %o", a, str1);
            $display("********************************************");
            $display("init bin val %b, str val %b", a, str2);
            $display("init hex val %h, str val %h", a, str2);
            $display("init dec val %d, str val %d", a, str2);
            $display("init oct val %o, str val %o", a, str2);      
        end
        always @(posedge clk) begin
            cyc <= cyc + 1;
            if (cyc == 1) begin
                c = 81'h2;
                d = 81'h3;
            end
            else if (cyc == 2) begin
                c = 81'h21ff11ff000001ff;
                d = 81'h21ff11ff001101ff;
            end
            else if (cyc == 3) begin
                c = 81'h21ff11ff21de32ff;
                d = 81'h21ff11ffe21921ff;
            end
            else if (cyc == 6) begin
                $write("*-* All Finished *-*\n");
                $finish;
            end
        end
        assign tmp = c & d;
        always @(tmp) begin
            str3 = tmp;
            $display("********************************************");
            $display("init bin val %b, str val %b", tmp, str3);
            $display("init hex val %h, str val %h", tmp, str3);
            $display("init dec val %d, str val %d", tmp, str3);
            $display("init oct val %o, str val %o", tmp, str3);        
        end
endmodule