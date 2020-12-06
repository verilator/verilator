module t ();
   logic [31:0] packed_data_32=0;
   byte         byte_in[4];
   initial  begin
      foreach (byte_in[i])     byte_in[i]     = byte'(i)+1;
      foreach (byte_in[i]) $display("byte_in[%0d]=%0h", i, byte_in[i]);
      packed_data_32    = {<<8{byte_in}};  
      $display("!!!! TEST: packed_data_32=%0h", packed_data_32); 
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
// byte_in[0]=1
//# byte_in[1]=2
//# byte_in[2]=3
//# byte_in[3]=4
//# !!!! TEST: packed_data_32=4030201