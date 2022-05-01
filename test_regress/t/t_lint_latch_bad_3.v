// DESCRIPTION: Verilator: Verilog Test module for Issue#1609
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Julien Margetts.

module t (/*AUTOARG*/ reset, a, b, c, en, o1, o2, o3, o4, o5);
   input  reset;
   input  a;
   input  b;
   input  c;
   input  en;
   output reg o1; // Always assigned
   output reg o2; //  "
   output reg o3; //  "
   output reg o4; //  "
   output reg o5; // Latch

always @(reset or en or a or b)
if (reset)
begin
    o1 = 1'b0;
    o2 = 1'b0;
    o3 = 1'b0;
    o4 = 1'b0;
    o5 <= 1'b0; // Do NOT expect Warning-COMBDLY
end
else
begin
    o1 = 1'b1;
    if (en)
    begin
        o2 = 1'b0;

            if (a)
            begin
            o3 = a;
            o5 <= 1'b1; // Do NOT expect Warning-COMBDLY
            end
            else
            begin
            o3 = ~a;
            o5 <=  a; // Do NOT expect Warning-COMBDLY
            end

        // o3 is not assigned in either path of this if/else
        // but no latch because always assigned above
            if (c)
            begin
            o2 = a ^ b;
            o4 = 1'b1;
        end
            else
            o4 = ~a ^ b;

        o2 = 1'b1;
    end
    else
    begin
        o2 = 1'b1;
            if (b)
        begin
            o3 = ~a | b;
            o5 <= ~b; // Do NOT expect Warning-COMBDLY
            end
            else
            begin
            o3 = a & ~b;
            // No assignment to o5, expect Warning-LATCH
            end
        o4 <= 1'b0; // expect Warning-COMBDLY
    end
end

endmodule
