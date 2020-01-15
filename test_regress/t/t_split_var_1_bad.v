module t();
    /*stray pragma */ /*verilator split_var*/

    // The following variables can not be splitted. will see warnings.
    real should_show_warning0;                 /*verilator split_var*/
    string should_show_warning1[0:2];          /*verilator split_var*/
    wire   should_show_warning2;               /*verilator split_var*/

    logic [3:0] addr;
    logic [7:0] rd_data0, rd_data1, rd_data2;

    sub0 i_sub0(.addr(addr), .rd_data(rd_data0));
    sub2 i_sub2(.addr(addr), .rd_data(rd_data2));

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


module sub2(input [3:0]addr, output logic [7:0] rd_data);

    logic [15:0] [7:0] cannot_split;  /*verilator split_var*/
    always_comb
        rd_data = cannot_split[addr];

endmodule

