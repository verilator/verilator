

module t();
/*stray pragma */ /*verilator split_var*/

// The following variables can not be splitted. will see warnings.
logic should_show_warning0;                /*verilator split_var*/
logic [1:0][7:0]should_show_warning1;      /*verilator split_var*/
wire  [7:0]should_show_warning2[0:1][0:3]; /*verilator split_var*/

logic [3:0] addr;
logic [7:0] rd_data;

sub0 i_sub0(.addr(addr), .rd_data(rd_data));


initial begin
    addr = 0;
    addr = 1;
    $finish;
end

endmodule


module sub0(input [3:0]addr, output logic [7:0] rd_data);

logic [7:0] cannot_split[0:15];  /*verilator split_var*/
always_comb
    rd_data = cannot_split[addr];

endmodule
