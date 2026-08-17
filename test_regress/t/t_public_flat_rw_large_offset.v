// DESCRIPTION: Verilator: Test public variable offsets larger than 32 bits

module t;
  longint padding1[1<<28];
  longint padding2[1<<28];
  longint padding3[1<<28];
endmodule
