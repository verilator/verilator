// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Johan Bjork.

interface intf;
    logic logic_in_intf;
    modport source(output logic_in_intf);
    modport sink(input logic_in_intf);
endinterface

module modify_interface
(
input logic value,
intf.source intf_inst
);
assign intf_inst.logic_in_intf = value;
endmodule

module t
#(
    parameter N = 6
)();
    intf ifs[N-1:0] ();
    logic [N-1:0] data;
    assign data = {1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1};

    generate
        genvar i;
        for (i = 0;i < 4; i++) begin
            assign ifs[i].logic_in_intf  = data[i];
        end
    endgenerate

    modify_interface m (
    	.value(data[4]),
    	.intf_inst(ifs[4]));

    modify_interface m1 (
    	.value(~ifs[4].logic_in_intf),
    	.intf_inst(ifs[5]));

    generate
        genvar j;
        for (j = 0;j < N-1; j++) begin
            initial begin
               if (ifs[j].logic_in_intf != data[j]) $stop;
            end
        end
    endgenerate

    initial begin
       if (ifs[5].logic_in_intf != ~ifs[4].logic_in_intf) $stop;
       $write("*-* All Finished *-*\n");
       $finish;
    end
endmodule
