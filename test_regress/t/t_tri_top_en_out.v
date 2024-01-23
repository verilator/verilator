module
   t_sub_io
     (
      inout my_io,
      input drv_en,
      input op_val
     );

   timeunit 1ns;
   timeprecision 1ps;

   assign my_io = drv_en ? op_val : 1'bz;

endmodule

module
   t_tri_top_en_out
     (
      inout single_bit_io,
      inout bidir_single_bit_io,
      inout [63:0] bus_64_io,
      inout [63:0] bidir_bus_64_io,
      inout [127:0] bus_128_io,
      inout [127:0] bidir_bus_128_io,
      input drv_en,
      inout sub_io
      );

   timeunit 1ns;
   timeprecision 1ps;

   bit 	    rand_bit;
   
   assign single_bit_io       = 1'bz;
   assign bidir_single_bit_io = drv_en ? rand_bit : 1'bz;
   assign bus_64_io           = {64{1'bz}};
   assign bidir_bus_64_io     = drv_en ? {64{rand_bit}} : {64{1'bz}};
   assign bus_128_io          = {128{1'bz}};
   assign bidir_bus_128_io    = drv_en ? {128{rand_bit}} : {128{1'bz}};

   initial
     begin
	rand_bit = (($urandom_range(1,0) & 'd1) == 'd1);
	#(1ns) $display("1ns");
	rand_bit = ~rand_bit;
	#(1ns) $display("2ns");
	rand_bit = ~rand_bit;
	#(1ns);
        $write("*-* All Finished *-*\n");
       	$finish(1);
     end

   final
     begin
	$display("All done at %t", $time);
     end
   
   always @(drv_en
	    or 
	    bidir_single_bit_io
	    or 
	    bidir_bus_64_io
	    or 
	    bidir_bus_128_io)
     begin
	$display("rand_bit = %b", rand_bit);
	if (drv_en)
	  begin
	     $display("bidir_single_bit_io = %b", bidir_single_bit_io);
	     $display("bidir_bus_64_io = %b", bidir_bus_64_io);
	     $display("bidir_bus_128_io = %b", bidir_bus_128_io);

	     if (bidir_single_bit_io != rand_bit)
	       begin
		  $display("%%Error: bidir_single_bit_io is wrong");
	       end

	     if (bidir_bus_64_io != {64{rand_bit}})
	       begin
		  $display("%%Error: bidir_bus_64_io is wrong");
		  $display("Should be bidir_bus_64_io = %b", {64{rand_bit}});
	       end

	     if (bidir_bus_128_io != {128{rand_bit}})
	       begin
		  $display("%%Error: bidir_bus_128_io is wrong");
		  $display("Should be bidir_bus_128 = %b", {128{rand_bit}});
	       end
	  end
     end
  
  t_sub_io 
    t_sub_io 
      (
       .my_io  (sub_io),
       .drv_en (drv_en),
       .op_val (rand_bit)
      );

endmodule
