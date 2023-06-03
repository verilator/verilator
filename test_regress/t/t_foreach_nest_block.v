// DESCRIPTION: Verilator: Verilog Test module
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Jomit626.
// SPDX-License-Identifier: CC0-1.0
//

module t();
    function static void func0();
        for(int i=0;i<16;i++) begin
        end
    endfunction

    task static task0(bit data[]);
        foreach (data[i]) begin
        end
    endtask

    task static task1(bit data[]);
        foreach (data[i]) begin
        end
    endtask

    bit [31:0] a0[];
    bit [31:0] a1[];

    initial begin
        foreach (a0[i]) begin
        end

        begin

          foreach (a1[i]) begin
          end

        end
    end

endmodule
