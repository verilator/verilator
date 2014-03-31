// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Iztok Jeras.

module t (/*AUTOARG*/);

   logic [3:0] array_simp [1:0] [3:0];  // big endian array

   initial begin
      array_simp[0] = '{ 4'd3, 4'd2, 4'd1, 4'd0};
      if ({array_simp[0][3],array_simp[0][2],array_simp[0][1],array_simp[0][0]} !== 16'h3210) $stop;

      // verilator lint_off WIDTH
      array_simp[0] = '{ 3 ,2 ,1, 0 };
      // verilator lint_on WIDTH
      if ({array_simp[0][3],array_simp[0][2],array_simp[0][1],array_simp[0][0]} !== 16'h3210) $stop;

      // Doesn't seem to work for unpacked arrays in other simulators
      //array_simp[0] = '{ 1:4'd3, default:13 };
      //if ({array_simp[0][3],array_simp[0][2],array_simp[0][1],array_simp[0][0]} !== 16'hDD3D) $stop;

      array_simp = '{ '{ 4'd3, 4'd2, 4'd1, 4'd0 }, '{ 4'd1, 4'd2, 4'd3, 4'd4 }};
      if ({array_simp[1][3],array_simp[1][2],array_simp[1][1],array_simp[1][0],
	   array_simp[0][3],array_simp[0][2],array_simp[0][1],array_simp[0][0]} !== 32'h3210_1234) $stop;

      // Doesn't seem to work for unpacked arrays in other simulators
      array_simp = '{2{ '{4'd3, 4'd2, 4'd1, 4'd0 } }};
      if ({array_simp[1][3],array_simp[1][2],array_simp[1][1],array_simp[1][0],
	   array_simp[0][3],array_simp[0][2],array_simp[0][1],array_simp[0][0]} !== 32'h3210_3210) $stop;

      array_simp = '{2{ '{4{ 4'd3 }} }};
      if ({array_simp[1][3],array_simp[1][2],array_simp[1][1],array_simp[1][0],
	   array_simp[0][3],array_simp[0][2],array_simp[0][1],array_simp[0][0]} !== 32'h3333_3333) $stop;

      // Not legal in other simulators - replication doesn't match
      // However IEEE suggests this is legal.
      //array_simp = '{2{ '{2{ 4'd3, 4'd2 }} }};  // Note it's not '{3,2}

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
