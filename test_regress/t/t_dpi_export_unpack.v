export "DPI-C" task readHEX;
export "DPI-C" task loadHEX;

task readHEX;
  input string file;
  output logic [7:0] stimuli[32'h00010000];
  $readmemh(file, stimuli);
endtask

task loadHEX;
  input string file;
  logic [7:0] stimuli[32'h00010000];
  readHEX(file, stimuli);
endtask

module tb();

  logic [7:0] result[32'h00010000];
  initial begin
    loadHEX("dummy");
  end

endmodule