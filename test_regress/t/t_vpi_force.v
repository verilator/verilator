// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

`define STRINGIFY(x) `"x`"

`ifdef VERILATOR_COMMENTS
`define PUBLIC_FORCEABLE /*verilator public_flat_rw*/  /*verilator forceable*/
`else
`define PUBLIC_FORCEABLE
`endif

module t;

  reg clk;

  initial begin
    clk = 0;
    forever #1 clk = ~clk;
  end

  Test test (.clk(clk));


endmodule

module Test (
    input clk
);

`ifdef IVERILOG
`elsif USE_VPI_NOT_DPI
`ifdef VERILATOR
`systemc_header
  extern "C" int putString();
  extern "C" int tryInvalidPutOperations();
  extern "C" int putInertialDelay();
  extern "C" int forceValues();
  extern "C" int releaseValues();
  extern "C" int releasePartiallyForcedValues();
  extern "C" int checkValuesForced();
  extern "C" int checkValuesPartiallyForced();
  extern "C" int checkValuesReleased();
`verilog
`endif
`else
`ifdef VERILATOR
  import "DPI-C" context function int putString();
  import "DPI-C" context function int tryInvalidPutOperations();
  import "DPI-C" context function int putInertialDelay();
`endif
  import "DPI-C" context function int forceValues();
  import "DPI-C" context function int releaseValues();
  import "DPI-C" context function int releasePartiallyForcedValues();
  import "DPI-C" context function int checkValuesPartiallyForced();
  import "DPI-C" context function int checkValuesForced();
  import "DPI-C" context function int checkValuesReleased();
`endif

  // Verify that vpi_put_value still works for strings
  string        str1       /*verilator public_flat_rw*/; // std::string

  // Verify that vpi_put_value still works with vpiInertialDelay
  logic [ 31:0] delayed    `PUBLIC_FORCEABLE; // IData

  // Clocked signals

  // Force with vpiIntVal
  logic         onebit     `PUBLIC_FORCEABLE; // CData
  logic [ 31:0] intval     `PUBLIC_FORCEABLE; // IData

  // Force with vpiVectorVal
  logic [  7:0] vectorC    `PUBLIC_FORCEABLE; // CData
  logic [ 61:0] vectorQ    `PUBLIC_FORCEABLE; // QData
  logic [127:0] vectorW    `PUBLIC_FORCEABLE; // VlWide

  // Force with vpiRealVal
  real          real1      `PUBLIC_FORCEABLE; // double

  // Force with vpiStringVal
  logic [ 15:0] textHalf   `PUBLIC_FORCEABLE; // SData
  logic [ 63:0] textLong   `PUBLIC_FORCEABLE; // QData
  logic [511:0] text       `PUBLIC_FORCEABLE; // VlWide

  // Force with vpiBinStrVal, vpiOctStrVal, vpiHexStrVal
  logic [ 7:0]  binString  `PUBLIC_FORCEABLE; // CData
  logic [ 14:0] octString  `PUBLIC_FORCEABLE; // SData
  logic [ 63:0] hexString  `PUBLIC_FORCEABLE; // QData

  // Force with vpiDecStrVal
  logic [  7:0] decStringC `PUBLIC_FORCEABLE; // CData
  logic [ 15:0] decStringS `PUBLIC_FORCEABLE; // SData
  logic [ 31:0] decStringI `PUBLIC_FORCEABLE; // IData
  logic [ 63:0] decStringQ `PUBLIC_FORCEABLE; // QData

  // Continuously assigned signals:

  // Force with vpiIntVal
  wire         onebitContinuously     `PUBLIC_FORCEABLE; // CData
  wire [ 31:0] intvalContinuously     `PUBLIC_FORCEABLE; // IData

  // Force with vpiVectorVal
  wire [  7:0] vectorCContinuously    `PUBLIC_FORCEABLE; // CData
  wire [ 61:0] vectorQContinuously    `PUBLIC_FORCEABLE; // QData
  wire [127:0] vectorWContinuously    `PUBLIC_FORCEABLE; // VlWide

  // Force with vpiRealVal
  `ifdef IVERILOG
  // Need wreal with Icarus for forcing continuously assigned real
  wreal        real1Continuously       `PUBLIC_FORCEABLE; // double
  `else
  real         real1Continuously       `PUBLIC_FORCEABLE; // double
  `endif

  // Force with vpiStringVal
  wire [ 15:0] textHalfContinuously   `PUBLIC_FORCEABLE; // SData
  wire [ 63:0] textLongContinuously   `PUBLIC_FORCEABLE; // QData
  wire [511:0] textContinuously       `PUBLIC_FORCEABLE; // VlWide

  // Force with vpiBinStrVal, vpiOctStrVal, vpiHexStrVal
  wire [ 7:0]  binStringContinuously  `PUBLIC_FORCEABLE; // CData
  wire [ 14:0] octStringContinuously  `PUBLIC_FORCEABLE; // SData
  wire [ 63:0] hexStringContinuously  `PUBLIC_FORCEABLE; // QData

  // Force with vpiDecStrVal
  wire [  7:0] decStringCContinuously `PUBLIC_FORCEABLE; // CData
  wire [ 15:0] decStringSContinuously `PUBLIC_FORCEABLE; // SData
  wire [ 31:0] decStringIContinuously `PUBLIC_FORCEABLE; // IData
  wire [ 63:0] decStringQContinuously `PUBLIC_FORCEABLE; // QData

  always @(posedge clk) begin
    onebit <= 1;
    intval <= 32'hAAAAAAAA;

    vectorC <= 8'hAA;
    vectorQ <= 62'h2AAAAAAA_AAAAAAAA;
    vectorW <= 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA;

    real1 <= 1.0;

    textHalf <= "Hf";
    textLong <= "Long64b";
    text <= "Verilog Test module";

    binString <= 8'b10101010;
    octString <= 15'o25252;  // 0b1010...
    hexString <= 64'hAAAAAAAAAAAAAAAA;  // 0b1010...

    decStringC <= 8'hAA;
    decStringS <= 16'hAAAA;
    decStringI <= 32'hAAAAAAAA;
    decStringQ <= 64'd12297829382473034410;  // 0b1010...
  end

  assign onebitContinuously = 1;
  assign intvalContinuously = 32'hAAAAAAAA;

  assign vectorCContinuously = 8'hAA;
  assign vectorQContinuously = 62'h2AAAAAAA_AAAAAAAA;
  assign vectorWContinuously = 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA;

  assign real1Continuously = 1.0;

  assign textHalfContinuously = "Hf";
  assign textLongContinuously = "Long64b";
  assign textContinuously = "Verilog Test module";

  assign binStringContinuously = 8'b10101010;
  assign octStringContinuously = 15'o25252;  // 0b1010...
  assign hexStringContinuously = 64'hAAAAAAAAAAAAAAAA;  // 0b1010...

  assign decStringCContinuously = 8'hAA;
  assign decStringSContinuously = 16'hAAAA;
  assign decStringIContinuously = 32'hAAAAAAAA;
  assign decStringQContinuously = 64'd12297829382473034410;  // 0b1010...

  task automatic svForceValues();
    force onebit = 0;
    force intval = 32'h55555555;
    force vectorC = 8'h55;
    force vectorQ = 62'h15555555_55555555;
    force vectorW = 128'h55555555_55555555_55555555_55555555;
    force real1 = 123456.789;
    force textHalf = "T2";
    force textLong = "44Four44";
    force text = "lorem ipsum";
    force binString = 8'b01010101;
    force octString = 15'o52525;
    force hexString = 64'h5555555555555555;
    force decStringC = 8'h55;
    force decStringS = 16'h5555;
    force decStringI = 32'h55555555;
    force decStringQ = 64'd6148914691236517205;

    force onebitContinuously = 0;
    force intvalContinuously = 32'h55555555;
    force vectorCContinuously = 8'h55;
    force vectorQContinuously = 62'h15555555_55555555;
    force vectorWContinuously = 128'h55555555_55555555_55555555_55555555;
    force real1Continuously = 123456.789;
    force textHalfContinuously = "T2";
    force textLongContinuously = "44Four44";
    force textContinuously = "lorem ipsum";
    force binStringContinuously = 8'b01010101;
    force octStringContinuously = 15'o52525;
    force hexStringContinuously = 64'h5555555555555555;
    force decStringCContinuously = 8'h55;
    force decStringSContinuously = 16'h5555;
    force decStringIContinuously = 32'h55555555;
    force decStringQContinuously = 64'd6148914691236517205;
  endtask

  task automatic svPartiallyForceValues();
    force intval[15:0] = 16'h5555;

    force vectorC[3:0] = 4'h5;
    force vectorQ[30:0] = 31'h55555555;
    force vectorW[63:0] = 64'h55555555_55555555;

    force textHalf[7:0] = "2";
    force textLong[31:0] = "ur44";
    force text[63:0] = "em ipsum";
    force binString[3:0] = 4'b0101;

    force octString[6:0] = 7'o125;
    force hexString[31:0] = 32'h55555555;

    force decStringC[3:0] = 4'h5;
    force decStringS[7:0] = 8'h55;
    force decStringI[15:0] = 16'h5555;
    force decStringQ[31:0] = 32'd1431655765;

    force intvalContinuously[15:0] = 16'h5555;

    force vectorCContinuously[3:0] = 4'h5;
    force vectorQContinuously[30:0] = 31'h55555555;
    force vectorWContinuously[63:0] = 64'h55555555_55555555;

    force textHalfContinuously[7:0] = "2";
    force textLongContinuously[31:0] = "ur44";
    force textContinuously[63:0] = "em ipsum";
    force binStringContinuously[3:0] = 4'b0101;

    force octStringContinuously[6:0] = 7'o125;
    force hexStringContinuously[31:0] = 32'h55555555;

    force decStringCContinuously[3:0] = 4'h5;
    force decStringSContinuously[7:0] = 8'h55;
    force decStringIContinuously[15:0] = 16'h5555;
    force decStringQContinuously[31:0] = 32'd1431655765;
  endtask

  task automatic vpiPutString();
    integer vpiStatus = 1;  // Default to failed status to ensure that a function *not* getting
                            // called also causes simulation termination
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("putString()");
`else
    vpiStatus = putString();
`endif
`else
    $stop; // This task only makes sense with Verilator, since other simulators ignore the "verilator forceable" metacomment.
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display(
          "C Test failed (vpi_put_value failed for string)");
      $stop;
    end
  endtask

  task automatic vpiTryInvalidPutOperations();
    integer vpiStatus = 1;  // Default to failed status to ensure that a function *not* getting
                            // called also causes simulation termination
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("tryInvalidPutOperations()");
`else
    vpiStatus = tryInvalidPutOperations();
`endif
`else
    $stop; // This task only makes sense with Verilator, since it tests verilated_vpi.cpp
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display(
          "C Test failed (invalid vpi_put_value operation either succeeded, even though it should have failed, or produced an unexpected error message.)");
      $stop;
    end
  endtask

  task automatic vpiPutInertialDelay();
    integer vpiStatus = 1;  // Default to failed status to ensure that a function *not* getting
                            // called also causes simulation termination
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("putInertialDelay()");
`else
    vpiStatus = putInertialDelay();
`endif
`else
    $stop; // This task only makes sense with Verilator, since it tests verilated_vpi.cpp
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display(
          "C Test failed (vpi_put_value with vpiInertialDelay failed)");
      $stop;
    end
  endtask

  task automatic vpiForceValues();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("forceValues()");
`else
    vpiStatus = forceValues();
`endif
`elsif IVERILOG
    vpiStatus = $forceValues;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $forceValues;
`else
    vpiStatus = forceValues();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (could not force value)");
      $stop;
    end
  endtask

  task automatic svReleaseValues();
    release onebit;
    release intval;
    release vectorC;
    release vectorQ;
    release vectorW;
    release real1;
    release textHalf;
    release textLong;
    release text;
    release binString;
    release octString;
    release hexString;
    release decStringC;
    release decStringS;
    release decStringI;
    release decStringQ;

    release onebitContinuously;
    release intvalContinuously;
    release vectorCContinuously;
    release vectorQContinuously;
    release vectorWContinuously;
    release real1Continuously;
    release textHalfContinuously;
    release textLongContinuously;
    release textContinuously;
    release binStringContinuously;
    release octStringContinuously;
    release hexStringContinuously;
    release decStringCContinuously;
    release decStringSContinuously;
    release decStringIContinuously;
    release decStringQContinuously;
  endtask

  task automatic vpiReleaseValues();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("releaseValues()");
`else
    vpiStatus = releaseValues();
`endif
`elsif IVERILOG
    vpiStatus = $releaseValues;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $releaseValues;
`else
    vpiStatus = releaseValues();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (could not release value)");
      $stop;
    end
  endtask

  task automatic vpiReleasePartiallyForcedValues();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("releasePartiallyForcedValues()");
`else
    vpiStatus = releasePartiallyForcedValues();
`endif
`elsif IVERILOG
    vpiStatus = $releasePartiallyForcedValues;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $releasePartiallyForcedValues;
`else
    vpiStatus = releasePartiallyForcedValues();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (could not release value)");
      $stop;
    end
  endtask

  task automatic svCheckValuesForced();
    if(onebit != 0) $stop;
    if(intval != 32'h55555555) $stop;
    if(vectorC != 8'h55) $stop;
    if(vectorQ != 62'h15555555_55555555) $stop;
    if(vectorW != 128'h55555555_55555555_55555555_55555555) $stop;
    if(real1 != 123456.789) $stop;
    if(textHalf != "T2") $stop;
    if(textLong != "44Four44") $stop;
    if(text != "lorem ipsum") $stop;
    if(binString != 8'b01010101) $stop;
    if(octString != 15'o52525) $stop;
    if(hexString != 64'h5555555555555555) $stop;
    if(decStringC != 8'h55) $stop;
    if(decStringS != 16'h5555) $stop;
    if(decStringI != 32'h55555555) $stop;
    if(decStringQ != 64'd6148914691236517205) $stop;

    if(onebitContinuously != 0) $stop;
    if(intvalContinuously != 32'h55555555) $stop;
    if(vectorCContinuously != 8'h55) $stop;
    if(vectorQContinuously != 62'h15555555_55555555) $stop;
    if(vectorWContinuously != 128'h55555555_55555555_55555555_55555555) $stop;
    if(real1Continuously != 123456.789) $stop;
    if(textHalfContinuously != "T2") $stop;
    if(textLongContinuously != "44Four44") $stop;
    if(textContinuously != "lorem ipsum") $stop;
    if(binStringContinuously != 8'b01010101) $stop;
    if(octStringContinuously != 15'o52525) $stop;
    if(hexStringContinuously != 64'h5555555555555555) $stop;
    if(decStringCContinuously != 8'h55) $stop;
    if(decStringSContinuously != 16'h5555) $stop;
    if(decStringIContinuously != 32'h55555555) $stop;
    if(decStringQContinuously != 64'd6148914691236517205) $stop;
  endtask

  task automatic vpiCheckValuesForced();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkValuesForced()");
`else
    vpiStatus = checkValuesForced();
`endif
`elsif IVERILOG
    vpiStatus = $checkValuesForced;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkValuesForced;
`else
    vpiStatus = checkValuesForced();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value after forcing does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckValuesPartiallyForced();
    if (intval != 32'hAAAA_5555) $stop;
    if (vectorC != 8'h A5) $stop;
    if (vectorQ != 62'h2AAAAAAAD5555555) $stop;
    if (vectorW != 128'hAAAAAAAA_AAAAAAAA_55555555_55555555) $stop;
    if (textHalf != "H2") $stop;
    if (textLong != "Lonur44") $stop;
    if (text != "Verilog Tesem ipsum") $stop;
    if (binString != 8'b1010_0101) $stop;
    if (octString != 15'b01010101_1010101) $stop;
    if (hexString != 64'hAAAAAAAA_55555555) $stop;
    if (decStringC != 8'hA5) $stop;
    if (decStringS != 16'hAA55) $stop;
    if (decStringI != 32'hAAAA_5555) $stop;
    if (decStringQ != 64'hAAAAAAAA_55555555) $stop;

    if (intvalContinuously != 32'hAAAA_5555) $stop;
    if (vectorCContinuously != 8'h A5) $stop;
    if (vectorQContinuously != 62'h2AAAAAAAD5555555) $stop;
    if (vectorWContinuously != 128'hAAAAAAAA_AAAAAAAA_55555555_55555555) $stop;
    if (textHalfContinuously != "H2") $stop;
    if (textLongContinuously != "Lonur44") $stop;
    if (textContinuously != "Verilog Tesem ipsum") $stop;
    if (binStringContinuously != 8'b1010_0101) $stop;
    if (octStringContinuously != 15'b01010101_1010101) $stop;
    if (hexStringContinuously != 64'hAAAAAAAA_55555555) $stop;
    if (decStringCContinuously != 8'hA5) $stop;
    if (decStringSContinuously != 16'hAA55) $stop;
    if (decStringIContinuously != 32'hAAAA_5555) $stop;
    if (decStringQContinuously != 64'hAAAAAAAA_55555555) $stop;
  endtask

  task automatic vpiCheckValuesPartiallyForced();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkValuesPartiallyForced()");
`else
    vpiStatus = checkValuesPartiallyForced();
`endif
`elsif IVERILOG
    vpiStatus = $checkValuesPartiallyForced;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkValuesPartiallyForced;
`else
    vpiStatus = checkValuesPartiallyForced();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value after partial forcing does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckValuesReleased();
    if (onebit != 1) $stop;
    if (intval != 32'hAAAAAAAA) $stop;
    if (vectorC != 8'hAA) $stop;
    if (vectorQ != 62'h2AAAAAAA_AAAAAAAA) $stop;
    if (vectorW != 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA) $stop;
    if (real1 != 1.0) $stop;
    if (textHalf != "Hf") $stop;
    if (textLong != "Long64b") $stop;
    if (text != "Verilog Test module") $stop;
    if (binString != 8'b10101010) $stop;
    if (octString != 15'o25252) $stop;
    if (hexString != 64'hAAAAAAAAAAAAAAAA) $stop;
    if (decStringC != 8'hAA) $stop;
    if (decStringS != 16'hAAAA) $stop;
    if (decStringI != 32'hAAAAAAAA) $stop;
    if (decStringQ != 64'd12297829382473034410) $stop;

    if (onebitContinuously != 1) $stop;
    if (intvalContinuously != 32'hAAAAAAAA) $stop;
    if (vectorCContinuously != 8'hAA) $stop;
    if (vectorQContinuously != 62'h2AAAAAAA_AAAAAAAA) $stop;
    if (vectorWContinuously != 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA) $stop;
    if (real1Continuously != 1.0) $stop;
    if (textHalfContinuously != "Hf") $stop;
    if (textLongContinuously != "Long64b") $stop;
    if (textContinuously != "Verilog Test module") $stop;
    if (binStringContinuously != 8'b10101010) $stop;
    if (octStringContinuously != 15'o25252) $stop;
    if (hexStringContinuously != 64'hAAAAAAAAAAAAAAAA) $stop;
    if (decStringCContinuously != 8'hAA) $stop;
    if (decStringSContinuously != 16'hAAAA) $stop;
    if (decStringIContinuously != 32'hAAAAAAAA) $stop;
    if (decStringQContinuously != 64'd12297829382473034410) $stop;
  endtask

  task automatic vpiCheckValuesReleased();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkValuesReleased()");
`else
    vpiStatus = checkValuesReleased();
`endif
`elsif IVERILOG
    vpiStatus = $checkValuesReleased;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkValuesReleased;
`else
    vpiStatus = checkValuesReleased();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value after releasing does not match expectation)");
      $stop;
    end
  endtask

  initial begin
`ifdef WAVES
$dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
`endif

`ifdef VERILATOR
    vpiPutString();
    vpiTryInvalidPutOperations();
    vpiPutInertialDelay();
`endif

    // Wait a bit before triggering the force to see a change in the traces
    #4 vpiForceValues();

    // Time delay to ensure setting and checking values does not happen
    // at the same time, so that the signals can have their values overwritten
    // by other processes
    #4 vpiCheckValuesForced();
    svCheckValuesForced();
    #4 vpiReleaseValues();
    #4 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Force through VPI, release through Verilog
    #4 vpiForceValues();
    #4 vpiCheckValuesForced();
    svCheckValuesForced();
    #4 svReleaseValues();
    #4 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Force through Verilog, release through VPI
    #4 svForceValues();
    #4 vpiCheckValuesForced();
    svCheckValuesForced();
    #4 vpiReleaseValues();
    #4 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Force only some bits, check if __VforceRd yields correct signal,
    // release through VPI
    #4 svPartiallyForceValues();
    #4 vpiCheckValuesPartiallyForced();
    svCheckValuesPartiallyForced();
    #4 vpiReleasePartiallyForcedValues();
    #4 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Force only some bits, check if __VforceRd yields correct signal,
    // release through Verilog
    #4 svPartiallyForceValues();
    #4 vpiCheckValuesPartiallyForced();
    svCheckValuesPartiallyForced();
    #4 svReleaseValues();
    #4 vpiCheckValuesReleased();
    svCheckValuesReleased();


    #5 $display("*-* All Finished *-*");
    $finish;
  end

`ifdef TEST_VERBOSE
  always @(posedge clk or negedge clk) begin
    $display("time: %0t\tclk:%b", $time, clk);

    $display("str1: %s", str1);
    $display("delayed: %x", delayed);

    $display("onebit: %x", onebit);
    $display("intval: %x", intval);
    $display("vectorC: %x", vectorC);
    $display("vectorQ: %x", vectorQ);
    $display("vectorW: %x", vectorW);
    $display("real1: %f", real1);
    $display("textHalf: %s", textHalf);
    $display("textLong: %s", textLong);
    $display("text: %s", text);
    $display("binString: %x", binString);
    $display("octString: %x", octString);
    $display("hexString: %x", hexString);
    $display("decStringC: %x", decStringC);
    $display("decStringS: %x", decStringS);
    $display("decStringI: %x", decStringI);
    $display("decStringQ: %x", decStringQ);

    $display("onebitContinuously: %x", onebitContinuously);
    $display("intvalContinuously: %x", intvalContinuously);
    $display("vectorCContinuously: %x", vectorCContinuously);
    $display("vectorQContinuously: %x", vectorQContinuously);
    $display("vectorWContinuously: %x", vectorWContinuously);
    $display("real1Continuously: %f", real1Continuously);
    $display("textHalfContinuously: %s", textHalfContinuously);
    $display("textLongContinuously: %s", textLongContinuously);
    $display("textContinuously: %s", textContinuously);
    $display("binStringContinuously: %x", binStringContinuously);
    $display("octStringContinuously: %x", octStringContinuously);
    $display("hexStringContinuously: %x", hexStringContinuously);
    $display("decStringCContinuously: %x", decStringCContinuously);
    $display("decStringSContinuously: %x", decStringSContinuously);
    $display("decStringIContinuously: %x", decStringIContinuously);
    $display("decStringQContinuously: %x", decStringQContinuously);

    $display("========================\n");
  end
`endif

endmodule
