// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Christian Hecken
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// verilog_format: on
`define STRINGIFY(x) `"x`"

`ifdef VERILATOR_COMMENTS
`define PUBLIC_FORCEABLE /*verilator public_flat_rw*/  /*verilator forceable*/
`else
`define PUBLIC_FORCEABLE
`endif

`ifdef TEST_VERBOSE
 `define verbose 1'b1
`else
 `define verbose 1'b0
`endif

module t;

  reg clk;

  initial begin
    clk = 0;
    forever #2 clk = ~clk;
  end

  Test test (.clk(clk));


endmodule

module Test (
    input clk
);

typedef enum byte {
    BitByIndex = 0,
    BitByName  = 1
} BitIndexingMethod;

typedef enum byte {
    DimByRepeatedIndex = 0,
    DimByMultiIndex = 1,
    DimByName = 2
} DimIndexingMethod;

typedef enum byte {
  Descending = 0,
  Ascending = 1
} Direction;


`ifdef IVERILOG
`elsif USE_VPI_NOT_DPI
`ifdef VERILATOR
`systemc_header
  extern "C" int putString();
  extern "C" int tryInvalidPutOperations();
  extern "C" int putInertialDelay();
  extern "C" int checkInertialDelay();
  extern "C" int forceValues(int dimIndexingMethod);
  extern "C" int partiallyForceValues(int direction);
  extern "C" int forceSingleBit(int bitIndexingMethod, int dimIndexingMethod);
  extern "C" int releaseValues(int dimIndexingMethod);
  extern "C" int releasePartiallyForcedValues(int dimIndexingMethod);
  extern "C" int releaseSingleBitForcedValues(int dimIndexingMethod);
  extern "C" int partiallyReleaseValues(int direction);
  extern "C" int releaseSingleBit(int bitIndexingMethod, int dimIndexingMethod);
  extern "C" int checkValuesForced();
  extern "C" int checkValuesPartiallyForced();
  extern "C" int checkSingleBitForced();
  extern "C" int checkValuesPartiallyReleased();
  extern "C" int checkSingleBitReleased();
  extern "C" int checkValuesReleased();
  extern "C" int checkNonContinuousValuesForced();
  extern "C" int checkContinuousValuesReleased();
  extern "C" int checkContinuousValuesPartiallyReleased();
  extern "C" int checkNonContinuousValuesPartiallyForced();
  extern "C" int checkContinuousValuesSingleBitReleased();
  extern "C" int checkNonContinuousSingleBitForced();
`verilog
`endif
`else
`ifdef VERILATOR
  import "DPI-C" context function int putString();
  import "DPI-C" context function int tryInvalidPutOperations();
  import "DPI-C" context function int putInertialDelay();
  import "DPI-C" context function int checkInertialDelay();
`endif
  import "DPI-C" context function int forceValues(input byte dimIndexingMethod);
  import "DPI-C" context function int partiallyForceValues(input byte direction);
  import "DPI-C" context function int forceSingleBit(input byte bitIndexingMethod, input byte dimIndexingMethod);
  import "DPI-C" context function int releaseValues(input byte dimIndexingMethod);
  import "DPI-C" context function int releasePartiallyForcedValues(input byte dimIndexingMethod);
  import "DPI-C" context function int releaseSingleBitForcedValues(input byte dimIndexingMethod);
  import "DPI-C" context function int partiallyReleaseValues(input byte direction);
  import "DPI-C" context function int releaseSingleBit(input byte bitIndexingMethod, input byte dimIndexingMethod);
  import "DPI-C" context function int checkValuesPartiallyForced();
  import "DPI-C" context function int checkSingleBitForced();
  import "DPI-C" context function int checkValuesPartiallyReleased();
  import "DPI-C" context function int checkValuesForced();
  import "DPI-C" context function int checkSingleBitReleased();
  import "DPI-C" context function int checkValuesReleased();
  import "DPI-C" context function int checkNonContinuousValuesForced();
  import "DPI-C" context function int checkContinuousValuesReleased();
  import "DPI-C" context function int checkContinuousValuesPartiallyReleased();
  import "DPI-C" context function int checkNonContinuousValuesPartiallyForced();
  import "DPI-C" context function int checkContinuousValuesSingleBitReleased();
  import "DPI-C" context function int checkNonContinuousSingleBitForced();
`endif

  // Verify that vpi_put_value still works for strings
  string        str1       /*verilator public_flat_rw*/; // std::string

  // Verify that EmitCSyms changes still allow for forceable, but not
  // public_flat_rw signals. This signal is only forced and checked in this
  // SystemVerilog testbench, but not through VPI.
  logic         nonPublic /*verilator forceable*/; // CData

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

  // Multidimensional signals - packed dimensions only for now, until forcing
  // unpacked signals is fully supported (#4735)
  // verilator lint_off ASCRANGE

  // These multidimensional packed arrays do not work well in Icarus:
  //   - Continuous assignments do not work
  //   - vpi_handle_by_multi_index is not implemented
  //   - vpi_handle_by_name and vpi_handle_by_index fail with negative indices
  //  Hence, these signals are excluded from testing with Icarus. Recommend
  //  Xcelium for cross-checking results.
`ifndef IVERILOG
  // Force the entire packed array (no partial forcing possible, because
  // partial indexing only works for bits, not dimension slices)
  logic [1:0][0:1][0:-1] packed2dC `PUBLIC_FORCEABLE; // CData
  logic [1:0][0:1][0:-3] packed2dS `PUBLIC_FORCEABLE; // SData
  logic [1:0][0:2][0:-3] packed2dI `PUBLIC_FORCEABLE; // IData
  logic [3:0][0:3][0:-3] packed2dQ `PUBLIC_FORCEABLE; // QData
  logic [3:0][0:3][0:-7] packed2dW `PUBLIC_FORCEABLE; // VlWide

  // Index into the first dimension and attempt to force all elements in it.
  // Should have the same effect as forcing the entire packed2d array,
  // while the other elements in the first dimension should stay unforced
  // Partial forcing is not possible here, because partial indexing only works
  // for bits, not dimension slices.
  logic [-1:-2][1:0][0:1][0:-1] packed3dS `PUBLIC_FORCEABLE; // SData
  logic [-1:-2][1:0][0:1][0:-3] packed3dI `PUBLIC_FORCEABLE; // IData
  logic [-1:-2][1:0][0:2][0:-3] packed3dQ `PUBLIC_FORCEABLE; // QData
  logic [-1:-2][3:0][0:3][0:-3] packed3dW `PUBLIC_FORCEABLE; // VlWide

  // Attempt to force only one element
  logic [-3:-3][2:2][-1:-1][3:0][0:-1]  packed4dC `PUBLIC_FORCEABLE; // CData
  logic [-3:-3][2:2][-1:-1][3:0][0:-3]  packed4dS `PUBLIC_FORCEABLE; // SData
  logic [-3:-3][2:2][-1:-1][3:0][0:-7]  packed4dI `PUBLIC_FORCEABLE; // IData
  logic [-3:-3][2:2][-1:-1][3:0][0:-15] packed4dQ `PUBLIC_FORCEABLE; // QData
  logic [-3:-3][2:2][-1:-1][3:0][0:-31] packed4dW `PUBLIC_FORCEABLE; // VlWide

  // Same as with packed4d*, but with ascending range
  logic [-3:-3][2:2][-1:-1][4:7][8:9]  ascPacked4dC `PUBLIC_FORCEABLE; // CData
  logic [-3:-3][2:2][-1:-1][4:7][8:11] ascPacked4dS `PUBLIC_FORCEABLE; // SData
  logic [-3:-3][2:2][-1:-1][4:7][8:15] ascPacked4dI `PUBLIC_FORCEABLE; // IData
  logic [-3:-3][2:2][-1:-1][4:7][8:23] ascPacked4dQ `PUBLIC_FORCEABLE; // QData
  logic [-3:-3][2:2][-1:-1][4:7][8:39] ascPacked4dW `PUBLIC_FORCEABLE; // VlWide
`endif

  // verilator lint_on ASCRANGE

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

  // Multidimensional signals (packed dimensions only for now)
  // verilator lint_off ASCRANGE

`ifndef IVERILOG // Continuous assignments to these signals do not work in Icarus
  // Force the entire packed array (no partial forcing possible, because
  // partial indexing only works for bits, not dimension slices)
  logic [1:0][0:1][0:-1] packed2dCContinuously `PUBLIC_FORCEABLE; // CData
  logic [1:0][0:1][0:-3] packed2dSContinuously `PUBLIC_FORCEABLE; // SData
  logic [1:0][0:2][0:-3] packed2dIContinuously `PUBLIC_FORCEABLE; // IData
  logic [3:0][0:3][0:-3] packed2dQContinuously `PUBLIC_FORCEABLE; // QData
  logic [3:0][0:3][0:-7] packed2dWContinuously `PUBLIC_FORCEABLE; // VlWide

  // Index into the first dimension and attempt to force all elements in it.
  // Should have the same effect as forcing the entire packed2d array,
  // while the other elements in the first dimension should stay unforced
  // Partial forcing is not possible here, because partial indexing only works
  // for bits, not dimension slices.
  logic [-1:-2][1:0][0:1][0:-1] packed3dSContinuously `PUBLIC_FORCEABLE; // SData
  logic [-1:-2][1:0][0:1][0:-3] packed3dIContinuously `PUBLIC_FORCEABLE; // IData
  logic [-1:-2][1:0][0:2][0:-3] packed3dQContinuously `PUBLIC_FORCEABLE; // QData
  logic [-1:-2][3:0][0:3][0:-3] packed3dWContinuously `PUBLIC_FORCEABLE; // VlWide

  // Fully index into the array and attempt to force only one element
  logic [-3:-3][2:2][-1:-1][3:0][0:-1]  packed4dCContinuously `PUBLIC_FORCEABLE; // CData
  logic [-3:-3][2:2][-1:-1][3:0][0:-3]  packed4dSContinuously `PUBLIC_FORCEABLE; // SData
  logic [-3:-3][2:2][-1:-1][3:0][0:-7]  packed4dIContinuously `PUBLIC_FORCEABLE; // IData
  logic [-3:-3][2:2][-1:-1][3:0][0:-15] packed4dQContinuously `PUBLIC_FORCEABLE; // QData
  logic [-3:-3][2:2][-1:-1][3:0][0:-31] packed4dWContinuously `PUBLIC_FORCEABLE; // VlWide

  // Same as with packed4d*, but with ascending range
  logic [-3:-3][2:2][-1:-1][4:7][8:9]  ascPacked4dCContinuously `PUBLIC_FORCEABLE; // CData
  logic [-3:-3][2:2][-1:-1][4:7][8:11] ascPacked4dSContinuously `PUBLIC_FORCEABLE; // SData
  logic [-3:-3][2:2][-1:-1][4:7][8:15] ascPacked4dIContinuously `PUBLIC_FORCEABLE; // IData
  logic [-3:-3][2:2][-1:-1][4:7][8:23] ascPacked4dQContinuously `PUBLIC_FORCEABLE; // QData
  logic [-3:-3][2:2][-1:-1][4:7][8:39] ascPacked4dWContinuously `PUBLIC_FORCEABLE; // VlWide
`endif

  // verilator lint_on ASCRANGE

  always @(posedge clk) begin
    nonPublic <= 1;

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

`ifndef IVERILOG
    packed2dC <= '{'{2'h2, 2'h2}, '{2'h2, 2'h2}};
    packed2dS <= '{'{4'hA, 4'hA}, '{4'hA, 4'hA}};
    packed2dI <= '{'{4'hA, 4'hA, 4'hA}, '{4'hA, 4'hA, 4'hA}};
    packed2dQ <= '{
        '{4'hA, 4'hA, 4'hA, 4'hA},
        '{4'hA, 4'hA, 4'hA, 4'hA},
        '{4'hA, 4'hA, 4'hA, 4'hA},
        '{4'hA, 4'hA, 4'hA, 4'hA}
    };
    packed2dW <= '{
        '{8'hAA, 8'hAA, 8'hAA, 8'hAA},
        '{8'hAA, 8'hAA, 8'hAA, 8'hAA},
        '{8'hAA, 8'hAA, 8'hAA, 8'hAA},
        '{8'hAA, 8'hAA, 8'hAA, 8'hAA}
    };

    packed3dS <= '{'{'{2'h2, 2'h2}, '{2'h2, 2'h2}}, '{'{2'h2, 2'h2}, '{2'h2, 2'h2}}};
    packed3dI <= '{'{'{4'hA, 4'hA}, '{4'hA, 4'hA}}, '{'{4'hA, 4'hA}, '{4'hA, 4'hA}}};
    packed3dQ <= '{
        '{'{4'hA, 4'hA, 4'hA}, '{4'hA, 4'hA, 4'hA}},
        '{'{4'hA, 4'hA, 4'hA}, '{4'hA, 4'hA, 4'hA}}
    };
    packed3dW <= '{
        '{
            '{4'hA, 4'hA, 4'hA, 4'hA},
            '{4'hA, 4'hA, 4'hA, 4'hA},
            '{4'hA, 4'hA, 4'hA, 4'hA},
            '{4'hA, 4'hA, 4'hA, 4'hA}
        },
        '{
            '{4'hA, 4'hA, 4'hA, 4'hA},
            '{4'hA, 4'hA, 4'hA, 4'hA},
            '{4'hA, 4'hA, 4'hA, 4'hA},
            '{4'hA, 4'hA, 4'hA, 4'hA}
        }
    };

    packed4dC <= '{'{'{'{2'h2, 2'h2, 2'h2, 2'h2}}}};
    packed4dS <= '{'{'{'{4'hA, 4'hA, 4'hA, 4'hA}}}};
    packed4dI <= '{'{'{'{8'hAA, 8'hAA, 8'hAA, 8'hAA}}}};
    packed4dQ <= '{'{'{'{16'hAAAA, 16'hAAAA, 16'hAAAA, 16'hAAAA}}}};
    packed4dW <= '{'{'{'{32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA}}}};

    ascPacked4dC <= '{'{'{'{2'h2, 2'h2, 2'h2, 2'h2}}}};
    ascPacked4dS <= '{'{'{'{4'hA, 4'hA, 4'hA, 4'hA}}}};
    ascPacked4dI <= '{'{'{'{8'hAA, 8'hAA, 8'hAA, 8'hAA}}}};
    ascPacked4dQ <= '{'{'{'{16'hAAAA, 16'hAAAA, 16'hAAAA, 16'hAAAA}}}};
    ascPacked4dW <= '{'{'{'{32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA}}}};
`endif
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

`ifndef IVERILOG
  assign packed2dCContinuously = '{'{2'h2, 2'h2}, '{2'h2, 2'h2}};
  assign packed2dSContinuously = '{'{4'hA, 4'hA}, '{4'hA, 4'hA}};
  assign packed2dIContinuously = '{'{4'hA, 4'hA, 4'hA}, '{4'hA, 4'hA, 4'hA}};
  assign packed2dQContinuously = '{
      '{4'hA, 4'hA, 4'hA, 4'hA},
      '{4'hA, 4'hA, 4'hA, 4'hA},
      '{4'hA, 4'hA, 4'hA, 4'hA},
      '{4'hA, 4'hA, 4'hA, 4'hA}
  };
  assign packed2dWContinuously = '{
      '{8'hAA, 8'hAA, 8'hAA, 8'hAA},
      '{8'hAA, 8'hAA, 8'hAA, 8'hAA},
      '{8'hAA, 8'hAA, 8'hAA, 8'hAA},
      '{8'hAA, 8'hAA, 8'hAA, 8'hAA}
  };

  assign packed3dSContinuously = '{'{'{2'h2, 2'h2}, '{2'h2, 2'h2}}, '{'{2'h2, 2'h2}, '{2'h2, 2'h2}}};
  assign packed3dIContinuously = '{'{'{4'hA, 4'hA}, '{4'hA, 4'hA}}, '{'{4'hA, 4'hA}, '{4'hA, 4'hA}}};
  assign packed3dQContinuously = '{
      '{'{4'hA, 4'hA, 4'hA}, '{4'hA, 4'hA, 4'hA}},
      '{'{4'hA, 4'hA, 4'hA}, '{4'hA, 4'hA, 4'hA}}
  };
  assign packed3dWContinuously = '{
      '{
          '{4'hA, 4'hA, 4'hA, 4'hA},
          '{4'hA, 4'hA, 4'hA, 4'hA},
          '{4'hA, 4'hA, 4'hA, 4'hA},
          '{4'hA, 4'hA, 4'hA, 4'hA}
      },
      '{
          '{4'hA, 4'hA, 4'hA, 4'hA},
          '{4'hA, 4'hA, 4'hA, 4'hA},
          '{4'hA, 4'hA, 4'hA, 4'hA},
          '{4'hA, 4'hA, 4'hA, 4'hA}
      }
  };

  assign packed4dCContinuously = '{'{'{'{2'h2, 2'h2, 2'h2, 2'h2}}}};
  assign packed4dSContinuously = '{'{'{'{4'hA, 4'hA, 4'hA, 4'hA}}}};
  assign packed4dIContinuously = '{'{'{'{8'hAA, 8'hAA, 8'hAA, 8'hAA}}}};
  assign packed4dQContinuously = '{'{'{'{16'hAAAA, 16'hAAAA, 16'hAAAA, 16'hAAAA}}}};
  assign packed4dWContinuously = '{'{'{'{32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA}}}};

  assign ascPacked4dCContinuously = '{'{'{'{2'h2, 2'h2, 2'h2, 2'h2}}}};
  assign ascPacked4dSContinuously = '{'{'{'{4'hA, 4'hA, 4'hA, 4'hA}}}};
  assign ascPacked4dIContinuously = '{'{'{'{8'hAA, 8'hAA, 8'hAA, 8'hAA}}}};
  assign ascPacked4dQContinuously = '{'{'{'{16'hAAAA, 16'hAAAA, 16'hAAAA, 16'hAAAA}}}};
  assign ascPacked4dWContinuously = '{'{'{'{32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA, 32'hAAAAAAAA}}}};
`endif

  task automatic svForceValues();
    force onebit = 0;
    force intval = 32'h55555555;
    force vectorC = 8'h55;
    force vectorQ = 62'h15555555_55555555;
    force vectorW = 128'h55555555_55555555_55555555_55555555;
    force real1 = 123456.789;
    force textHalf = "T3";
    force textLong = "44Four44";
    force text = "lorem ipsum";
    force binString = 8'b01010101;
    force octString = 15'o52525;
    force hexString = 64'h5555555555555555;
    force decStringC = 8'h55;
    force decStringS = 16'h5555;
    force decStringI = 32'h55555555;
    force decStringQ = 64'd6148914691236517205;

`ifndef IVERILOG
    force packed2dC = '{'{2'h1, 2'h1}, '{2'h1, 2'h1}};
    force packed2dS = '{'{4'h5, 4'h5}, '{4'h5, 4'h5}};
    force packed2dI = '{'{4'h5, 4'h5, 4'h5}, '{4'h5, 4'h5, 4'h5}};
    force packed2dQ = '{
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5}
        };
    force packed2dW = '{
            '{8'h55, 8'h55, 8'h55, 8'h55},
            '{8'h55, 8'h55, 8'h55, 8'h55},
            '{8'h55, 8'h55, 8'h55, 8'h55},
            '{8'h55, 8'h55, 8'h55, 8'h55}
        };

    force packed3dS[-2] = '{'{2'h1, 2'h1}, '{2'h1, 2'h1}};
    force packed3dI[-2] = '{'{4'h5, 4'h5}, '{4'h5, 4'h5}};
    force packed3dQ[-2] = '{'{4'h5, 4'h5, 4'h5}, '{4'h5, 4'h5, 4'h5}};
    force packed3dW[-2] = '{
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5}
        };

    force packed4dC[-3][2][-1][2] = 2'h1;
    force packed4dS[-3][2][-1][2] = 4'h5;
    force packed4dI[-3][2][-1][2] = 8'h55;
    force packed4dQ[-3][2][-1][2] = 16'h5555;
    force packed4dW[-3][2][-1][2] = 32'h55555555;

    // For equivalent results as with packed4d* (i.e. forcing the second
    // element from the left), force element 5 in the ascending range [4:7],
    // which corresponds to index 2 in the descending range [3:0]
    force ascPacked4dC[-3][2][-1][5] = 2'h1;
    force ascPacked4dS[-3][2][-1][5] = 4'h5;
    force ascPacked4dI[-3][2][-1][5] = 8'h55;
    force ascPacked4dQ[-3][2][-1][5] = 16'h5555;
    force ascPacked4dW[-3][2][-1][5] = 32'h55555555;
`endif

    force onebitContinuously = 0;
    force intvalContinuously = 32'h55555555;
    force vectorCContinuously = 8'h55;
    force vectorQContinuously = 62'h15555555_55555555;
    force vectorWContinuously = 128'h55555555_55555555_55555555_55555555;
    force real1Continuously = 123456.789;
    force textHalfContinuously = "T3";
    force textLongContinuously = "44Four44";
    force textContinuously = "lorem ipsum";
    force binStringContinuously = 8'b01010101;
    force octStringContinuously = 15'o52525;
    force hexStringContinuously = 64'h5555555555555555;
    force decStringCContinuously = 8'h55;
    force decStringSContinuously = 16'h5555;
    force decStringIContinuously = 32'h55555555;
    force decStringQContinuously = 64'd6148914691236517205;

`ifndef IVERILOG
    force packed2dCContinuously = '{'{2'h1, 2'h1}, '{2'h1, 2'h1}};
    force packed2dSContinuously = '{'{4'h5, 4'h5}, '{4'h5, 4'h5}};
    force packed2dIContinuously = '{'{4'h5, 4'h5, 4'h5}, '{4'h5, 4'h5, 4'h5}};
    force packed2dQContinuously = '{
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5}
        };
    force packed2dWContinuously = '{
            '{8'h55, 8'h55, 8'h55, 8'h55},
            '{8'h55, 8'h55, 8'h55, 8'h55},
            '{8'h55, 8'h55, 8'h55, 8'h55},
            '{8'h55, 8'h55, 8'h55, 8'h55}
        };

    force packed3dSContinuously[-2] = '{'{2'h1, 2'h1}, '{2'h1, 2'h1}};
    force packed3dIContinuously[-2] = '{'{4'h5, 4'h5}, '{4'h5, 4'h5}};
    force packed3dQContinuously[-2] = '{'{4'h5, 4'h5, 4'h5}, '{4'h5, 4'h5, 4'h5}};
    force packed3dWContinuously[-2] = '{
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5},
            '{4'h5, 4'h5, 4'h5, 4'h5}
        };

    force packed4dCContinuously[-3][2][-1][2] = 2'h1;
    force packed4dSContinuously[-3][2][-1][2] = 4'h5;
    force packed4dIContinuously[-3][2][-1][2] = 8'h55;
    force packed4dQContinuously[-3][2][-1][2] = 16'h5555;
    force packed4dWContinuously[-3][2][-1][2] = 32'h55555555;

    force ascPacked4dCContinuously[-3][2][-1][5] = 2'h1;
    force ascPacked4dSContinuously[-3][2][-1][5] = 4'h5;
    force ascPacked4dIContinuously[-3][2][-1][5] = 8'h55;
    force ascPacked4dQContinuously[-3][2][-1][5] = 16'h5555;
    force ascPacked4dWContinuously[-3][2][-1][5] = 32'h55555555;
`endif
  endtask

  task automatic svPartiallyForceValues();
    force intval[15:0] = 16'h5555;

    force vectorC[3:0] = 4'h5;
    force vectorQ[30:0] = 31'h55555555;
    force vectorW[63:0] = 64'h55555555_55555555;

    force textHalf[7:0] = "3";
    force textLong[31:0] = "ur44";
    force text[79:0] = "orem ipsum"; // VlWide part select
    force binString[3:0] = 4'b0101;

    force octString[6:0] = 7'o125;
    force hexString[31:0] = 32'h55555555;

    force decStringC[3:0] = 4'h5;
    force decStringS[7:0] = 8'h55;
    force decStringI[15:0] = 16'h5555;
    force decStringQ[31:0] = 32'd1431655765;

`ifndef XRUN // Partial forcing multidimensional signals works only through SystemVerilog with Xrun, but not through VPI, so don't test it at all
`ifndef IVERILOG
    force packed4dC[-3][2][-1][2][-1:-1] = 1'h1;
    force packed4dS[-3][2][-1][2][-2:-3] = 2'h1;
    force packed4dI[-3][2][-1][2][-4:-7] = 4'h5;
    force packed4dQ[-3][2][-1][2][-8:-15] = 8'h55;
    force packed4dW[-3][2][-1][2][-16:-31] = 16'h5555;

    force ascPacked4dC[-3][2][-1][5][9:9] = 1'h1;
    force ascPacked4dS[-3][2][-1][5][10:11] = 2'h1;
    force ascPacked4dI[-3][2][-1][5][12:15] = 4'h5;
    force ascPacked4dQ[-3][2][-1][5][16:23] = 8'h55;
    force ascPacked4dW[-3][2][-1][5][24:39] = 16'h5555;
`endif
`endif

    force intvalContinuously[15:0] = 16'h5555;

    force vectorCContinuously[3:0] = 4'h5;
    force vectorQContinuously[30:0] = 31'h55555555;
    force vectorWContinuously[63:0] = 64'h55555555_55555555;

    force textHalfContinuously[7:0] = "3";
    force textLongContinuously[31:0] = "ur44";
    force textContinuously[79:0] = "orem ipsum";
    force binStringContinuously[3:0] = 4'b0101;

    force octStringContinuously[6:0] = 7'o125;
    force hexStringContinuously[31:0] = 32'h55555555;

    force decStringCContinuously[3:0] = 4'h5;
    force decStringSContinuously[7:0] = 8'h55;
    force decStringIContinuously[15:0] = 16'h5555;
    force decStringQContinuously[31:0] = 32'd1431655765;

`ifndef XRUN
`ifndef IVERILOG
    force packed4dCContinuously[-3][2][-1][2][-1:-1] = 1'h1;
    force packed4dSContinuously[-3][2][-1][2][-2:-3] = 2'h1;
    force packed4dIContinuously[-3][2][-1][2][-4:-7] = 4'h5;
    force packed4dQContinuously[-3][2][-1][2][-8:-15] = 8'h55;
    force packed4dWContinuously[-3][2][-1][2][-16:-31] = 16'h5555;

    force ascPacked4dCContinuously[-3][2][-1][5][9:9] = 1'h1;
    force ascPacked4dSContinuously[-3][2][-1][5][10:11] = 2'h1;
    force ascPacked4dIContinuously[-3][2][-1][5][12:15] = 4'h5;
    force ascPacked4dQContinuously[-3][2][-1][5][16:23] = 8'h55;
    force ascPacked4dWContinuously[-3][2][-1][5][24:39] = 16'h5555;
`endif
`endif
  endtask

  task automatic svForceSingleBit();
    force intval[0] = 1;
    force vectorC[0] = 1;
    force vectorQ[0] = 1;
    force vectorW[0] = 1;
    force textHalf[0] = 1;
    force textLong[1] = 0; // "b" = 'b01100010, force second-to-last bit to 0
    force text[3] = 1; // "e" = 'b01100101, force bit 3 to 1
    force binString[0] = 1;
    force octString[0] = 1;
    force hexString[0] = 1;
    force decStringC[0] = 1;
    force decStringS[0] = 1;
    force decStringI[0] = 1;
    force decStringQ[0] = 1;
`ifndef IVERILOG
    force packed4dC[-3][2][-1][2][-1] = 1;
    force packed4dS[-3][2][-1][2][-3] = 1;
    force packed4dI[-3][2][-1][2][-7] = 1;
    force packed4dQ[-3][2][-1][2][-15] = 1;
    force packed4dW[-3][2][-1][2][-31] = 1;

    force ascPacked4dC[-3][2][-1][5][9] = 1;
    force ascPacked4dS[-3][2][-1][5][11] = 1;
    force ascPacked4dI[-3][2][-1][5][15] = 1;
    force ascPacked4dQ[-3][2][-1][5][23] = 1;
    force ascPacked4dW[-3][2][-1][5][39] = 1;
`endif

    force intvalContinuously[0] = 1;
    force vectorCContinuously[0] = 1;
    force vectorQContinuously[0] = 1;
    force vectorWContinuously[0] = 1;
    force textHalfContinuously[0] = 1;
    force textLongContinuously[1] = 0; // "b" = 'b01100010, force second-to-last bit to 0
    force textContinuously[3] = 1; // "e" = 'b01100101, force bit 3 to 1
    force binStringContinuously[0] = 1;
    force octStringContinuously[0] = 1;
    force hexStringContinuously[0] = 1;
    force decStringCContinuously[0] = 1;
    force decStringSContinuously[0] = 1;
    force decStringIContinuously[0] = 1;
    force decStringQContinuously[0] = 1;
`ifndef IVERILOG
    force packed4dCContinuously[-3][2][-1][2][-1] = 1;
    force packed4dSContinuously[-3][2][-1][2][-3] = 1;
    force packed4dIContinuously[-3][2][-1][2][-7] = 1;
    force packed4dQContinuously[-3][2][-1][2][-15] = 1;
    force packed4dWContinuously[-3][2][-1][2][-31] = 1;

    force ascPacked4dCContinuously[-3][2][-1][5][9] = 1;
    force ascPacked4dSContinuously[-3][2][-1][5][11] = 1;
    force ascPacked4dIContinuously[-3][2][-1][5][15] = 1;
    force ascPacked4dQContinuously[-3][2][-1][5][23] = 1;
    force ascPacked4dWContinuously[-3][2][-1][5][39] = 1;
`endif
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

  task automatic vpiCheckInertialDelay();
    integer vpiStatus = 1;  // Default to failed status to ensure that a function *not* getting
                            // called also causes simulation termination
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkInertialDelay()");
`else
    vpiStatus = checkInertialDelay();
`endif
`else
    $stop; // This task only makes sense with Verilator, since it tests verilated_vpi.cpp
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display(
          "C Test failed (vpi_get_value to check result of previous vpi_put_value with vpiInertialDelay failed)");
      $stop;
    end
  endtask

  task automatic vpiForceValues(DimIndexingMethod dimIndexingMethod);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("forceValues(",dimIndexingMethod,")");
`else
    vpiStatus = forceValues(dimIndexingMethod);
`endif
`elsif IVERILOG
    vpiStatus = $forceValues(dimIndexingMethod);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $forceValues(dimIndexingMethod);
`else
    vpiStatus = forceValues(dimIndexingMethod);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      if (dimIndexingMethod == DimByRepeatedIndex) begin
        $display("C Test failed (could not force value using vpi_handle_by_index)");
      end else if (dimIndexingMethod == DimByMultiIndex) begin
        $display("C Test failed (could not force value using vpi_handle_by_multi_index)");
      end else begin
        $display("C Test failed (could not force value using vpi_handle_by_name)");
      end
      $stop;
    end
  endtask

  task automatic vpiPartiallyForceValues(Direction direction);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("partiallyForceValues(",direction,")");
`else
    vpiStatus = partiallyForceValues(direction);
`endif
`elsif IVERILOG
    vpiStatus = $partiallyForceValues(direction);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $partiallyForceValues(direction);
`else
    vpiStatus = partiallyForceValues(direction);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $write("C Test failed (could not partially force value in ");
      if (direction == Ascending) begin
        $write("ascending");
      end else begin
        $write("descending");
      end
      $write(" bit order");
      $display(")");
      $stop;
    end
  endtask

  task automatic vpiForceSingleBit(BitIndexingMethod bitIndexingMethod, DimIndexingMethod dimIndexingMethod);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("forceSingleBit(",bitIndexingMethod,",",dimIndexingMethod,")");
`else
    vpiStatus = forceSingleBit(bitIndexingMethod, dimIndexingMethod);
`endif
`elsif IVERILOG
    vpiStatus = $forceSingleBit(bitIndexingMethod, dimIndexingMethod);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $forceSingleBit(bitIndexingMethod, dimIndexingMethod);
`else
    vpiStatus = forceSingleBit(bitIndexingMethod, dimIndexingMethod);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $write("C Test failed (could not force single bit value using ");
      if(dimIndexingMethod == DimByRepeatedIndex) begin
        $write("vpi_handle_by_index");
      end else if (dimIndexingMethod == DimByMultiIndex) begin
        $write("vpi_handle_by_multi_index");
      end else begin
        $write("vpi_handle_by_name");
      end
      $write(" dimension indexing and ");
      if (bitIndexingMethod == BitByIndex) begin
        $write("vpi_handle_by_index");
      end else begin
        $write("vpi_handle_by_name");
      end
      $write(" bit indexing");
      $display(")");
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
`ifndef IVERILOG
    release packed2dC;
    release packed2dS;
    release packed2dI;
    release packed2dQ;
    release packed2dW;
    release packed3dS[-2];
    release packed3dI[-2];
    release packed3dQ[-2];
    release packed3dW[-2];
    release packed4dC[-3][2][-1][2];
    release packed4dS[-3][2][-1][2];
    release packed4dI[-3][2][-1][2];
    release packed4dQ[-3][2][-1][2];
    release packed4dW[-3][2][-1][2];
    release ascPacked4dC[-3][2][-1][5];
    release ascPacked4dS[-3][2][-1][5];
    release ascPacked4dI[-3][2][-1][5];
    release ascPacked4dQ[-3][2][-1][5];
    release ascPacked4dW[-3][2][-1][5];
`endif

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
`ifndef IVERILOG
    release packed2dCContinuously;
    release packed2dSContinuously;
    release packed2dIContinuously;
    release packed2dQContinuously;
    release packed2dWContinuously;
    release packed3dSContinuously[-2];
    release packed3dIContinuously[-2];
    release packed3dQContinuously[-2];
    release packed3dWContinuously[-2];
    release packed4dCContinuously[-3][2][-1][2];
    release packed4dSContinuously[-3][2][-1][2];
    release packed4dIContinuously[-3][2][-1][2];
    release packed4dQContinuously[-3][2][-1][2];
    release packed4dWContinuously[-3][2][-1][2];
    release ascPacked4dCContinuously[-3][2][-1][5];
    release ascPacked4dSContinuously[-3][2][-1][5];
    release ascPacked4dIContinuously[-3][2][-1][5];
    release ascPacked4dQContinuously[-3][2][-1][5];
    release ascPacked4dWContinuously[-3][2][-1][5];
`endif
  endtask

  task automatic vpiReleaseValues(DimIndexingMethod dimIndexingMethod);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("releaseValues(",dimIndexingMethod,")");
`else
    vpiStatus = releaseValues(dimIndexingMethod);
`endif
`elsif IVERILOG
    vpiStatus = $releaseValues(dimIndexingMethod);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $releaseValues(dimIndexingMethod);
`else
    vpiStatus = releaseValues(dimIndexingMethod);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      if (dimIndexingMethod == DimByRepeatedIndex) begin
        $display("C Test failed (could not release value using vpi_handle_by_index)");
      end else if (dimIndexingMethod == DimByMultiIndex) begin
        $display("C Test failed (could not release value using vpi_handle_by_multi_index)");
      end else begin
        $display("C Test failed (could not release value using vpi_handle_by_name)");
      end
      $stop;
    end
  endtask

  task automatic svPartiallyReleaseValues();
    release intval[15:0];

    release vectorC[3:0];
    release vectorQ[30:0];
    release vectorW[63:0];

    release textHalf[7:0];
    release textLong[31:0];
    release text[79:0];
    release binString[3:0];

    release octString[6:0];
    release hexString[31:0];

    release decStringC[3:0];
    release decStringS[7:0];
    release decStringI[15:0];
    release decStringQ[31:0];

`ifndef IVERILOG
    release packed4dC[-3][2][-1][2][-1:-1];
    release packed4dS[-3][2][-1][2][-2:-3];
    release packed4dI[-3][2][-1][2][-4:-7];
    release packed4dQ[-3][2][-1][2][-8:-15];
    release packed4dW[-3][2][-1][2][-16:-31];

    release ascPacked4dC[-3][2][-1][5][9:9];
    release ascPacked4dS[-3][2][-1][5][10:11];
    release ascPacked4dI[-3][2][-1][5][12:15];
    release ascPacked4dQ[-3][2][-1][5][16:23];
    release ascPacked4dW[-3][2][-1][5][24:39];
`endif

    release intvalContinuously[15:0];

    release vectorCContinuously[3:0];
    release vectorQContinuously[30:0];
    release vectorWContinuously[63:0];

    release textHalfContinuously[7:0];
    release textLongContinuously[31:0];
    release textContinuously[79:0];
    release binStringContinuously[3:0];

    release octStringContinuously[6:0];
    release hexStringContinuously[31:0];

    release decStringCContinuously[3:0];
    release decStringSContinuously[7:0];
    release decStringIContinuously[15:0];
    release decStringQContinuously[31:0];

`ifndef IVERILOG
    release packed4dCContinuously[-3][2][-1][2][-1:-1];
    release packed4dSContinuously[-3][2][-1][2][-2:-3];
    release packed4dIContinuously[-3][2][-1][2][-4:-7];
    release packed4dQContinuously[-3][2][-1][2][-8:-15];
    release packed4dWContinuously[-3][2][-1][2][-16:-31];

    release ascPacked4dCContinuously[-3][2][-1][5][9:9];
    release ascPacked4dSContinuously[-3][2][-1][5][10:11];
    release ascPacked4dIContinuously[-3][2][-1][5][12:15];
    release ascPacked4dQContinuously[-3][2][-1][5][16:23];
    release ascPacked4dWContinuously[-3][2][-1][5][24:39];
`endif
  endtask

  task automatic vpiPartiallyReleaseValues(Direction direction);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("partiallyReleaseValues(",direction,")");
`else
    vpiStatus = partiallyReleaseValues(direction);
`endif
`elsif IVERILOG
    vpiStatus = $partiallyReleaseValues(direction);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $partiallyReleaseValues(direction);
`else
    vpiStatus = partiallyReleaseValues(direction);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $write("C Test failed (could not partially release value in ");
      if (direction == Ascending) begin
        $write("ascending");
      end else begin
        $write("descending");
      end
      $write(" bit order");
      $display(")");
      $stop;
    end
  endtask

  task automatic vpiReleasePartiallyForcedValues(DimIndexingMethod dimIndexingMethod);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("releasePartiallyForcedValues(",dimIndexingMethod,")");
`else
    vpiStatus = releasePartiallyForcedValues(dimIndexingMethod);
`endif
`elsif IVERILOG
    vpiStatus = $releasePartiallyForcedValues(dimIndexingMethod);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $releasePartiallyForcedValues(dimIndexingMethod);
`else
    vpiStatus = releasePartiallyForcedValues(dimIndexingMethod);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      if (dimIndexingMethod == DimByRepeatedIndex) begin
        $display("C Test failed (could not release partially forced value using vpi_handle_by_index)");
      end else if (dimIndexingMethod == DimByMultiIndex) begin
        $display("C Test failed (could not release partially forced value using vpi_handle_by_multi_index)");
      end else begin
        $display("C Test failed (could not release partially forced value using vpi_handle_by_name)");
      end
      $stop;
    end
  endtask

  task automatic svReleaseSingleBit();
    release intval[0];
    release vectorC[0];
    release vectorQ[0];
    release vectorW[0];
    release textHalf[0];
    release textLong[1];
    release text[3];
    release binString[0];
    release octString[0];
    release hexString[0];
    release decStringC[0];
    release decStringS[0];
    release decStringI[0];
    release decStringQ[0];
`ifndef IVERILOG
    release packed4dC[-3][2][-1][2][-1];
    release packed4dS[-3][2][-1][2][-3];
    release packed4dI[-3][2][-1][2][-7];
    release packed4dQ[-3][2][-1][2][-15];
    release packed4dW[-3][2][-1][2][-31];

    release ascPacked4dC[-3][2][-1][5][9];
    release ascPacked4dS[-3][2][-1][5][11];
    release ascPacked4dI[-3][2][-1][5][15];
    release ascPacked4dQ[-3][2][-1][5][23];
    release ascPacked4dW[-3][2][-1][5][39];
`endif

    release intvalContinuously[0];
    release vectorCContinuously[0];
    release vectorQContinuously[0];
    release vectorWContinuously[0];
    release textHalfContinuously[0];
    release textLongContinuously[1];
    release textContinuously[3];
    release binStringContinuously[0];
    release octStringContinuously[0];
    release hexStringContinuously[0];
    release decStringCContinuously[0];
    release decStringSContinuously[0];
    release decStringIContinuously[0];
    release decStringQContinuously[0];
`ifndef IVERILOG
    release packed4dCContinuously[-3][2][-1][2][-1];
    release packed4dSContinuously[-3][2][-1][2][-3];
    release packed4dIContinuously[-3][2][-1][2][-7];
    release packed4dQContinuously[-3][2][-1][2][-15];
    release packed4dWContinuously[-3][2][-1][2][-31];

    release ascPacked4dCContinuously[-3][2][-1][5][9];
    release ascPacked4dSContinuously[-3][2][-1][5][11];
    release ascPacked4dIContinuously[-3][2][-1][5][15];
    release ascPacked4dQContinuously[-3][2][-1][5][23];
    release ascPacked4dWContinuously[-3][2][-1][5][39];
`endif
  endtask

  task automatic vpiReleaseSingleBit(BitIndexingMethod bitIndexingMethod, DimIndexingMethod dimIndexingMethod);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("releaseSingleBit(",bitIndexingMethod,",",dimIndexingMethod,")");
`else
    vpiStatus = releaseSingleBit(bitIndexingMethod, dimIndexingMethod);
`endif
`elsif IVERILOG
    vpiStatus = $releaseSingleBit(bitIndexingMethod, dimIndexingMethod);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $releaseSingleBit(bitIndexingMethod, dimIndexingMethod);
`else
    vpiStatus = releaseSingleBit(bitIndexingMethod, dimIndexingMethod);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $write("C Test failed (could not release single bit value using ");
      if(dimIndexingMethod == DimByRepeatedIndex) begin
        $write("vpi_handle_by_index");
      end else if (dimIndexingMethod == DimByMultiIndex) begin
        $write("vpi_handle_by_multi_index");
      end else begin
        $write("vpi_handle_by_name");
      end
      $write(" dimension indexing and ");
      if (bitIndexingMethod == BitByIndex) begin
        $write("vpi_handle_by_index");
      end else begin
        $write("vpi_handle_by_name");
      end
      $write(" bit indexing");
      $display(")");
      $stop;
    end
  endtask

  // Release the *entire* signal, whereas vpiReleaseSingleBit only releases
  // the single bit that was forced
  task automatic vpiReleaseSingleBitForcedValues(DimIndexingMethod dimIndexingMethod);
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("releaseSingleBitForcedValues(",dimIndexingMethod,")");
`else
    vpiStatus = releaseSingleBitForcedValues(dimIndexingMethod);
`endif
`elsif IVERILOG
    vpiStatus = $releaseSingleBitForcedValues(dimIndexingMethod);
`elsif USE_VPI_NOT_DPI
    vpiStatus = $releaseSingleBitForcedValues(dimIndexingMethod);
`else
    vpiStatus = releaseSingleBitForcedValues(dimIndexingMethod);
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      if (dimIndexingMethod == DimByRepeatedIndex) begin
        $display("C Test failed (could not use vpi_handle_by_index to release values that had single bit forced)");
      end else if (dimIndexingMethod == DimByMultiIndex) begin
        $display("C Test failed (could not use vpi_handle_by_multi_index to release values that had single bit forced)");
      end else begin
        $display("C Test failed (could not use vpi_handle_by_name to release values that had single bit forced)");
      end
      $stop;
    end
  endtask

  task automatic svCheckValuesForced();
    svCheckNonContinuousValuesForced();

    `checkh(onebitContinuously, 0);
    `checkh(intvalContinuously, 32'h55555555);
    `checkh(vectorCContinuously, 8'h55);
    `checkh(vectorQContinuously, 62'h15555555_55555555);
    `checkh(vectorWContinuously, 128'h55555555_55555555_55555555_55555555);
    `checkr(real1Continuously, 123456.789);
    `checks(textHalfContinuously, "T3");
    `checks(textLongContinuously, "44Four44");
    `checks(textContinuously, "lorem ipsum");
    `checkh(binStringContinuously, 8'b01010101);
    `checkh(octStringContinuously, 15'o52525);
    `checkh(hexStringContinuously, 64'h5555555555555555);
    `checkh(decStringCContinuously, 8'h55);
    `checkh(decStringSContinuously, 16'h5555);
    `checkh(decStringIContinuously, 32'h55555555);
    `checkh(decStringQContinuously, 64'd6148914691236517205);
`ifndef IVERILOG
    `checkh(packed2dCContinuously, 8'h55);
    `checkh(packed2dSContinuously, 16'h5555);
    `checkh(packed2dIContinuously, 24'h555555);
    `checkh(packed2dQContinuously, 64'h55555555_55555555);
    `checkh(packed2dWContinuously, 128'h55555555_55555555_55555555_55555555);
    `checkh(packed3dSContinuously, 16'hAA55);
    `checkh(packed3dIContinuously, 32'hAAAA5555);
    `checkh(packed3dQContinuously, 48'hAAAAAA_555555);
    `checkh(packed3dWContinuously, 128'hAAAAAAAA_AAAAAAAA_55555555_55555555);

    // Forced only element 2 of the [3:0] dimension
    `checkh(packed4dCContinuously, 8'b10_01_10_10);
    `checkh(packed4dSContinuously, 16'hA_5_A_A);
    `checkh(packed4dIContinuously, 32'hAA_55_AA_AA);
    `checkh(packed4dQContinuously, 64'hAAAA_5555_AAAA_AAAA);
    `checkh(packed4dWContinuously, 128'hAAAAAAAA_55555555_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dCContinuously, 8'b10_01_10_10);
    `checkh(ascPacked4dSContinuously, 16'hA_5_A_A);
    `checkh(ascPacked4dIContinuously, 32'hAA_55_AA_AA);
    `checkh(ascPacked4dQContinuously, 64'hAAAA_5555_AAAA_AAAA);
    `checkh(ascPacked4dWContinuously, 128'hAAAAAAAA_55555555_AAAAAAAA_AAAAAAAA);
`endif
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

  task automatic svCheckNonContinuousValuesForced();
    `checkh(onebit, 0);
    `checkh(intval, 32'h55555555);
    `checkh(vectorC, 8'h55);
    `checkh(vectorQ, 62'h15555555_55555555);
    `checkh(vectorW, 128'h55555555_55555555_55555555_55555555);
    `checkr(real1, 123456.789);
    `checks(textHalf, "T3");
    `checks(textLong, "44Four44");
    `checks(text, "lorem ipsum");
    `checkh(binString, 8'b01010101);
    `checkh(octString, 15'o52525);
    `checkh(hexString, 64'h5555555555555555);
    `checkh(decStringC, 8'h55);
    `checkh(decStringS, 16'h5555);
    `checkh(decStringI, 32'h55555555);
    `checkh(decStringQ, 64'd6148914691236517205);
`ifndef IVERILOG
    `checkh(packed2dC, 8'h55);
    `checkh(packed2dS, 16'h5555);
    `checkh(packed2dI, 24'h555555);
    `checkh(packed2dQ, 64'h55555555_55555555);
    `checkh(packed2dW, 128'h55555555_55555555_55555555_55555555);
    `checkh(packed3dS, 16'hAA55);
    `checkh(packed3dI, 32'hAAAA5555);
    `checkh(packed3dQ, 48'hAAAAAA_555555);
    `checkh(packed3dW, 128'hAAAAAAAA_AAAAAAAA_55555555_55555555);
    `checkh(packed4dC, 8'b10_01_10_10);
    `checkh(packed4dS, 16'hA_5_A_A);
    `checkh(packed4dI, 32'hAA_55_AA_AA);
    `checkh(packed4dQ, 64'hAAAA_5555_AAAA_AAAA);
    `checkh(packed4dW, 128'hAAAAAAAA_55555555_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dC, 8'b10_01_10_10);
    `checkh(ascPacked4dS, 16'hA_5_A_A);
    `checkh(ascPacked4dI, 32'hAA_55_AA_AA);
    `checkh(ascPacked4dQ, 64'hAAAA_5555_AAAA_AAAA);
    `checkh(ascPacked4dW, 128'hAAAAAAAA_55555555_AAAAAAAA_AAAAAAAA);
`endif
  endtask

  // Check that the values *after releasing* still have the forced value
  task automatic vpiCheckNonContinuousValuesForced();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkNonContinuousValuesForced()");
`else
    vpiStatus = checkNonContinuousValuesForced();
`endif
`elsif IVERILOG
    vpiStatus = $checkNonContinuousValuesForced;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkNonContinuousValuesForced;
`else
    vpiStatus = checkNonContinuousValuesForced();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value of non-continuously assigned signal after releasing does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckContinuousValuesReleased();
    `checkh(onebitContinuously, 1);
    `checkh(intvalContinuously, 32'hAAAAAAAA);
    `checkh(vectorCContinuously, 8'hAA);
    `checkh(vectorQContinuously, 62'h2AAAAAAA_AAAAAAAA);
    `checkh(vectorWContinuously, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
    `checkr(real1Continuously, 1.0);
    `checks(textHalfContinuously, "Hf");
    `checks(textLongContinuously, "Long64b");
    `checks(textContinuously, "Verilog Test module");
    `checkh(binStringContinuously, 8'b10101010);
    `checkh(octStringContinuously, 15'o25252);
    `checkh(hexStringContinuously, 64'hAAAAAAAAAAAAAAAA);
    `checkh(decStringCContinuously, 8'hAA);
    `checkh(decStringSContinuously, 16'hAAAA);
    `checkh(decStringIContinuously, 32'hAAAAAAAA);
    `checkh(decStringQContinuously, 64'd12297829382473034410);
`ifndef IVERILOG
    `checkh(packed2dCContinuously, 8'hAA);
    `checkh(packed2dSContinuously, 16'hAAAA);
    `checkh(packed2dIContinuously, 24'hAAAAAA);
    `checkh(packed2dQContinuously, 64'hAAAAAAAA_AAAAAAAA);
    `checkh(packed2dWContinuously, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
    `checkh(packed3dSContinuously, 16'hAAAA);
    `checkh(packed3dIContinuously, 32'hAAAAAAAA);
    `checkh(packed3dQContinuously, 48'hAAAAAA_AAAAAA);
    `checkh(packed3dWContinuously, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
    `checkh(packed4dCContinuously, 8'hAA);
    `checkh(packed4dSContinuously, 16'hAAAA);
    `checkh(packed4dIContinuously, 32'hAAAAAAAA);
    `checkh(packed4dQContinuously, 64'hAAAAAAAA_AAAAAAAA);
    `checkh(packed4dWContinuously, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dCContinuously, 8'hAA);
    `checkh(ascPacked4dSContinuously, 16'hAAAA);
    `checkh(ascPacked4dIContinuously, 32'hAAAAAAAA);
    `checkh(ascPacked4dQContinuously, 64'hAAAAAAAA_AAAAAAAA);
    `checkh(ascPacked4dWContinuously, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
`endif
  endtask

  task automatic vpiCheckContinuousValuesReleased();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkContinuousValuesReleased()");
`else
    vpiStatus = checkContinuousValuesReleased();
`endif
`elsif IVERILOG
    vpiStatus = $checkContinuousValuesReleased;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkContinuousValuesReleased;
`else
    vpiStatus = checkContinuousValuesReleased();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value of continuously assigned signal after releasing does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckValuesPartiallyForced();
    svCheckNonContinuousValuesPartiallyForced();

    `checkh(intvalContinuously, 32'hAAAA_5555);
    `checkh(vectorCContinuously, 8'h A5);
    `checkh(vectorQContinuously, 62'h2AAAAAAAD5555555);
    `checkh(vectorWContinuously, 128'hAAAAAAAA_AAAAAAAA_55555555_55555555);
    `checks(textHalfContinuously, "H3");
    `checks(textLongContinuously, "Lonur44");
    `checks(textContinuously, "Verilog Torem ipsum");
    `checkh(binStringContinuously, 8'b1010_0101);
    `checkh(octStringContinuously, 15'b01010101_1010101);
    `checkh(hexStringContinuously, 64'hAAAAAAAA_55555555);
    `checkh(decStringCContinuously, 8'hA5);
    `checkh(decStringSContinuously, 16'hAA55);
    `checkh(decStringIContinuously, 32'hAAAA_5555);
    `checkh(decStringQContinuously, 64'hAAAAAAAA_55555555);

`ifndef XRUN // Xcelium does not support a syntax like "signal[1][0][1:0]" in vpi_handle_by_name
`ifndef IVERILOG
    // Forced only the lower bits of element 2 of the [3:0] dimension
    `checkh(packed4dCContinuously, 8'b10_11_10_10);
    `checkh(packed4dSContinuously, 16'b1010_1001_1010_1010);
    `checkh(packed4dIContinuously, 32'hAA_A5_AA_AA);
    `checkh(packed4dQContinuously, 64'hAAAA_AA55_AAAA_AAAA);
    `checkh(packed4dWContinuously, 128'hAAAAAAAA_AAAA5555_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dCContinuously, 8'b10_11_10_10);
    `checkh(ascPacked4dSContinuously, 16'b1010_1001_1010_1010);
    `checkh(ascPacked4dIContinuously, 32'hAA_A5_AA_AA);
    `checkh(ascPacked4dQContinuously, 64'hAAAA_AA55_AAAA_AAAA);
    `checkh(ascPacked4dWContinuously, 128'hAAAAAAAA_AAAA5555_AAAAAAAA_AAAAAAAA);
`endif
`endif
  endtask

  task automatic svCheckSingleBitForced();
    svCheckNonContinuousSingleBitForced();

    `checkh(intvalContinuously, 32'hAAAAAAAB);
    `checkh(vectorCContinuously, 8'hAB);
    `checkh(vectorQContinuously, 62'h2AAAAAAA_AAAAAAAB);
    `checkh(vectorWContinuously, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAB);
    `checks(textHalfContinuously, "Hg");
    `checks(textLongContinuously, "Long64`");
    `checks(textContinuously, "Verilog Test modulm");
    `checkh(binStringContinuously, 8'b10101011);
    `checkh(octStringContinuously, 15'o25253);
    `checkh(hexStringContinuously, 64'hAAAAAAAAAAAAAAAB);
    `checkh(decStringCContinuously, 8'hAB);
    `checkh(decStringSContinuously, 16'hAAAB);
    `checkh(decStringIContinuously, 32'hAAAAAAAB);
    `checkh(decStringQContinuously, 64'd12297829382473034411);

`ifndef IVERILOG
    // Forced only the LSB of element 2 of the [3:0] dimension
    `checkh(packed4dCContinuously, 8'b10_11_10_10);
    `checkh(packed4dSContinuously, 16'hA_B_A_A);
    `checkh(packed4dIContinuously, 32'hAA_AB_AA_AA);
    `checkh(packed4dQContinuously, 64'hAAAA_AAAB_AAAA_AAAA);
    `checkh(packed4dWContinuously, 128'hAAAAAAAA_AAAAAAAB_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dCContinuously, 8'b10_11_10_10);
    `checkh(ascPacked4dSContinuously, 16'hA_B_A_A);
    `checkh(ascPacked4dIContinuously, 32'hAA_AB_AA_AA);
    `checkh(ascPacked4dQContinuously, 64'hAAAA_AAAB_AAAA_AAAA);
    `checkh(ascPacked4dWContinuously, 128'hAAAAAAAA_AAAAAAAB_AAAAAAAA_AAAAAAAA);
`endif
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

  task automatic vpiCheckSingleBitForced();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkSingleBitForced()");
`else
    vpiStatus = checkSingleBitForced();
`endif
`elsif IVERILOG
    vpiStatus = $checkSingleBitForced;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkSingleBitForced;
`else
    vpiStatus = checkSingleBitForced();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value of after forcing single bit does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckNonContinuousValuesPartiallyForced();
    `checkh(intval, 32'hAAAA_5555);
    `checkh(vectorC, 8'h A5);
    `checkh(vectorQ, 62'h2AAAAAAAD5555555);
    `checkh(vectorW, 128'hAAAAAAAA_AAAAAAAA_55555555_55555555);
    `checks(textHalf, "H3");
    `checks(textLong, "Lonur44");
    `checks(text, "Verilog Torem ipsum");
    `checkh(binString, 8'b1010_0101);
    `checkh(octString, 15'b01010101_1010101);
    `checkh(hexString, 64'hAAAAAAAA_55555555);
    `checkh(decStringC, 8'hA5);
    `checkh(decStringS, 16'hAA55);
    `checkh(decStringI, 32'hAAAA_5555);
    `checkh(decStringQ, 64'hAAAAAAAA_55555555);

`ifndef IVERILOG
`ifndef XRUN
    // Forced only the lower bits of element 2 of the [3:0] dimension
    `checkh(packed4dC, 8'b10_11_10_10);
    `checkh(packed4dS, 16'b1010_1001_1010_1010);
    `checkh(packed4dI, 32'hAA_A5_AA_AA);
    `checkh(packed4dQ, 64'hAAAA_AA55_AAAA_AAAA);
    `checkh(packed4dW, 128'hAAAAAAAA_AAAA5555_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dC, 8'b10_11_10_10);
    `checkh(ascPacked4dS, 16'b1010_1001_1010_1010);
    `checkh(ascPacked4dI, 32'hAA_A5_AA_AA);
    `checkh(ascPacked4dQ, 64'hAAAA_AA55_AAAA_AAAA);
    `checkh(ascPacked4dW, 128'hAAAAAAAA_AAAA5555_AAAAAAAA_AAAAAAAA);
`endif
`endif
  endtask

  // Check that the values *after releasing* still have the partially forced value
  task automatic vpiCheckNonContinuousValuesPartiallyForced();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkNonContinuousValuesPartiallyForced()");
`else
    vpiStatus = checkNonContinuousValuesPartiallyForced();
`endif
`elsif IVERILOG
    vpiStatus = $checkNonContinuousValuesPartiallyForced;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkNonContinuousValuesPartiallyForced;
`else
    vpiStatus = checkNonContinuousValuesPartiallyForced();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value of non-continuously assigned signal after releasing from partial force does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckNonContinuousSingleBitForced();
    `checkh(intval, 32'hAAAAAAAB);
    `checkh(vectorC, 8'hAB);
    `checkh(vectorQ, 62'h2AAAAAAA_AAAAAAAB);
    `checkh(vectorW, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAB);
    `checks(textHalf, "Hg");
    `checks(textLong, "Long64`");
    `checks(text, "Verilog Test modulm");
    `checkh(binString, 8'b10101011);
    `checkh(octString, 15'o25253);
    `checkh(hexString, 64'hAAAAAAAAAAAAAAAB);
    `checkh(decStringC, 8'hAB);
    `checkh(decStringS, 16'hAAAB);
    `checkh(decStringI, 32'hAAAAAAAB);
    `checkh(decStringQ, 64'd12297829382473034411);

`ifndef IVERILOG
    // Forced only the LSB of element 2 of the [3:0] dimension
    `checkh(packed4dC, 8'b10_11_10_10);
    `checkh(packed4dS, 16'hA_B_A_A);
    `checkh(packed4dI, 32'hAA_AB_AA_AA);
    `checkh(packed4dQ, 64'hAAAA_AAAB_AAAA_AAAA);
    `checkh(packed4dW, 128'hAAAAAAAA_AAAAAAAB_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dC, 8'b10_11_10_10);
    `checkh(ascPacked4dS, 16'hA_B_A_A);
    `checkh(ascPacked4dI, 32'hAA_AB_AA_AA);
    `checkh(ascPacked4dQ, 64'hAAAA_AAAB_AAAA_AAAA);
    `checkh(ascPacked4dW, 128'hAAAAAAAA_AAAAAAAB_AAAAAAAA_AAAAAAAA);
`endif
  endtask

  task automatic vpiCheckNonContinuousSingleBitForced();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkNonContinuousSingleBitForced()");
`else
    vpiStatus = checkNonContinuousSingleBitForced();
`endif
`elsif IVERILOG
    vpiStatus = $checkNonContinuousSingleBitForced;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkNonContinuousSingleBitForced;
`else
    vpiStatus = checkNonContinuousSingleBitForced();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value of continuously assigned signal after releasing single bit does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckValuesReleased();
    `checkh(onebit, 1);
    `checkh(intval, 32'hAAAAAAAA);
    `checkh(vectorC, 8'hAA);
    `checkh(vectorQ, 62'h2AAAAAAA_AAAAAAAA);
    `checkh(vectorW, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
    `checkr(real1, 1.0);
    `checks(textHalf, "Hf");
    `checks(textLong, "Long64b");
    `checks(text, "Verilog Test module");
    `checkh(binString, 8'b10101010);
    `checkh(octString, 15'o25252);
    `checkh(hexString, 64'hAAAAAAAAAAAAAAAA);
    `checkh(decStringC, 8'hAA);
    `checkh(decStringS, 16'hAAAA);
    `checkh(decStringI, 32'hAAAAAAAA);
    `checkh(decStringQ, 64'd12297829382473034410);
`ifndef IVERILOG
    `checkh(packed2dC, 8'hAA);
    `checkh(packed2dS, 16'hAAAA);
    `checkh(packed2dI, 24'hAAAAAA);
    `checkh(packed2dQ, 64'hAAAAAAAA_AAAAAAAA);
    `checkh(packed2dW, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
    `checkh(packed3dS, 16'hAAAA);
    `checkh(packed3dI, 32'hAAAAAAAA);
    `checkh(packed3dQ, 48'hAAAAAA_AAAAAA);
    `checkh(packed3dW, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
    `checkh(packed4dC, 8'hAA);
    `checkh(packed4dS, 16'hAAAA);
    `checkh(packed4dI, 32'hAAAAAAAA);
    `checkh(packed4dQ, 64'hAAAAAAAA_AAAAAAAA);
    `checkh(packed4dW, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dC, 8'hAA);
    `checkh(ascPacked4dS, 16'hAAAA);
    `checkh(ascPacked4dI, 32'hAAAAAAAA);
    `checkh(ascPacked4dQ, 64'hAAAAAAAA_AAAAAAAA);
    `checkh(ascPacked4dW, 128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA);
`endif

    svCheckContinuousValuesReleased();
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

  task automatic svCheckValuesPartiallyReleased();
    `checkh(intval, 'h5555aaaa);
    `checkh(vectorC, 'h5a);
    `checkh(vectorQ, 'h155555552aaaaaaa);
    `checkh(vectorW, 'h5555555555555555aaaaaaaaaaaaaaaa);
    `checks(textHalf, "Tf");
    `checks(textLong, "44Fog64b");
    `checks(text, "lest module");
    `checkh(octString,'h552a);
    `checkh(hexString,'h55555555aaaaaaaa);
    `checkh(decStringC,'h5a);
    `checkh(decStringS,'h55aa);
    `checkh(decStringI,'h5555aaaa);
    `checkh(decStringQ,'h55555555aaaaaaaa);

`ifndef IVERILOG
`ifndef XRUN
    // Only element 2 of the [3:0] dimension was forced, then only the lower
    // bits of that element were released
    `checkh(packed4dC, 8'b10_00_10_10);
    `checkh(packed4dS, 16'b1010_0110_1010_1010);
    `checkh(packed4dI, 32'hAA_5A_AA_AA);
    `checkh(packed4dQ, 64'hAAAA_55AA_AAAA_AAAA);
    `checkh(packed4dW, 128'hAAAAAAAA_5555AAAA_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dC, 8'b10_00_10_10);
    `checkh(ascPacked4dS, 16'b1010_0110_1010_1010);
    `checkh(ascPacked4dI, 32'hAA_5A_AA_AA);
    `checkh(ascPacked4dQ, 64'hAAAA_55AA_AAAA_AAAA);
    `checkh(ascPacked4dW, 128'hAAAAAAAA_5555AAAA_AAAAAAAA_AAAAAAAA);
`endif
`endif

    svCheckContinuousValuesPartiallyReleased();
  endtask

  task automatic svCheckContinuousValuesPartiallyReleased();
    `checkh(intvalContinuously, 'h5555aaaa);
    `checkh(vectorCContinuously, 'h5a);
    `checkh(vectorQContinuously, 'h155555552aaaaaaa);
    `checkh(vectorWContinuously, 'h5555555555555555aaaaaaaaaaaaaaaa);
    `checks(textHalfContinuously, "Tf");
    `checks(textLongContinuously, "44Fog64b");
    `checks(textContinuously, "lest module");
    `checkh(octStringContinuously,'h552a);
    `checkh(hexStringContinuously,'h55555555aaaaaaaa);
    `checkh(decStringCContinuously,'h5a);
    `checkh(decStringSContinuously,'h55aa);
    `checkh(decStringIContinuously,'h5555aaaa);
    `checkh(decStringQContinuously,'h55555555aaaaaaaa);

`ifndef IVERILOG
`ifndef XRUN
    // Only element 2 of the [3:0] dimension was forced, then only the lower
    // bits of that element were released
    `checkh(packed4dCContinuously, 8'b10_00_10_10);
    `checkh(packed4dSContinuously, 16'b1010_0110_1010_1010);
    `checkh(packed4dIContinuously, 32'hAA_5A_AA_AA);
    `checkh(packed4dQContinuously, 64'hAAAA_55AA_AAAA_AAAA);
    `checkh(packed4dWContinuously, 128'hAAAAAAAA_5555AAAA_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dCContinuously, 8'b10_00_10_10);
    `checkh(ascPacked4dSContinuously, 16'b1010_0110_1010_1010);
    `checkh(ascPacked4dIContinuously, 32'hAA_5A_AA_AA);
    `checkh(ascPacked4dQContinuously, 64'hAAAA_55AA_AAAA_AAAA);
    `checkh(ascPacked4dWContinuously, 128'hAAAAAAAA_5555AAAA_AAAAAAAA_AAAAAAAA);
`endif
`endif
  endtask

  task automatic vpiCheckValuesPartiallyReleased();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkValuesPartiallyReleased()");
`else
    vpiStatus = checkValuesPartiallyReleased();
`endif
`elsif IVERILOG
    vpiStatus = $checkValuesPartiallyReleased;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkValuesPartiallyReleased;
`else
    vpiStatus = checkValuesPartiallyReleased();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value after partial releasing does not match expectation)");
      $stop;
    end
  endtask

  task automatic vpiCheckContinuousValuesPartiallyReleased();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkContinuousValuesPartiallyReleased()");
`else
    vpiStatus = checkContinuousValuesPartiallyReleased();
`endif
`elsif IVERILOG
    vpiStatus = $checkContinuousValuesPartiallyReleased;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkContinuousValuesPartiallyReleased;
`else
    vpiStatus = checkContinuousValuesPartiallyReleased();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value of continuously assigned signal after partial releasing does not match expectation)");
      $stop;
    end
  endtask

 task automatic svCheckContinuousValuesSingleBitReleased();
    `checkh(intvalContinuously, 32'h55555554);
    `checkh(vectorCContinuously, 8'h54);
    `checkh(vectorQContinuously, 62'h15555555_55555554);
    `checkh(vectorWContinuously, 128'h55555555_55555555_55555555_55555554);
    `checks(textHalfContinuously, "T2");
    `checks(textLongContinuously, "44Four46");
    `checks(textContinuously, "lorem ipsue");
    `checkh(binStringContinuously, 8'b01010100);
    `checkh(octStringContinuously, 15'o52524);
    `checkh(hexStringContinuously, 64'h5555555555555554);
    `checkh(decStringCContinuously, 8'h54);
    `checkh(decStringSContinuously, 16'h5554);
    `checkh(decStringIContinuously, 32'h55555554);
    `checkh(decStringQContinuously, 64'd6148914691236517204);

`ifndef IVERILOG
    // Only element 2 of the [3:0] dimension was forced, then only the LSB
    // of that element was released
    `checkh(packed4dCContinuously, 8'b10_00_10_10);
    `checkh(packed4dSContinuously, 16'b1010_0100_1010_1010);
    `checkh(packed4dIContinuously, 32'hAA_54_AA_AA);
    `checkh(packed4dQContinuously, 64'hAAAA_5554_AAAA_AAAA);
    `checkh(packed4dWContinuously, 128'hAAAAAAAA_55555554_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dCContinuously, 8'b10_00_10_10);
    `checkh(ascPacked4dSContinuously, 16'b1010_0100_1010_1010);
    `checkh(ascPacked4dIContinuously, 32'hAA_54_AA_AA);
    `checkh(ascPacked4dQContinuously, 64'hAAAA_5554_AAAA_AAAA);
    `checkh(ascPacked4dWContinuously, 128'hAAAAAAAA_55555554_AAAAAAAA_AAAAAAAA);
`endif
  endtask

  task automatic vpiCheckContinuousValuesSingleBitReleased();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkContinuousValuesSingleBitReleased()");
`else
    vpiStatus = checkContinuousValuesSingleBitReleased();
`endif
`elsif IVERILOG
    vpiStatus = $checkContinuousValuesSingleBitReleased;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkContinuousValuesSingleBitReleased;
`else
    vpiStatus = checkContinuousValuesSingleBitReleased();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value of continuously assigned signal after releasing single bit does not match expectation)");
      $stop;
    end
  endtask

  task automatic svCheckSingleBitReleased();
    `checkh(intval, 32'h55555554);
    `checkh(vectorC, 8'h54);
    `checkh(vectorQ, 62'h15555555_55555554);
    `checkh(vectorW, 128'h55555555_55555555_55555555_55555554);
    `checks(textHalf, "T2");
    `checks(textLong, "44Four46");
    `checks(text, "lorem ipsue");
    `checkh(binString, 8'b01010100);
    `checkh(octString, 15'o52524);
    `checkh(hexString, 64'h5555555555555554);
    `checkh(decStringC, 8'h54);
    `checkh(decStringS, 16'h5554);
    `checkh(decStringI, 32'h55555554);
    `checkh(decStringQ, 64'd6148914691236517204);

`ifndef IVERILOG
    // Only element 2 of the [3:0] dimension was forced, then only the LSB
    // of that element was released
    `checkh(packed4dC, 8'b10_00_10_10);
    `checkh(packed4dS, 16'b1010_0100_1010_1010);
    `checkh(packed4dI, 32'hAA_54_AA_AA);
    `checkh(packed4dQ, 64'hAAAA_5554_AAAA_AAAA);
    `checkh(packed4dW, 128'hAAAAAAAA_55555554_AAAAAAAA_AAAAAAAA);

    `checkh(ascPacked4dC, 8'b10_00_10_10);
    `checkh(ascPacked4dS, 16'b1010_0100_1010_1010);
    `checkh(ascPacked4dI, 32'hAA_54_AA_AA);
    `checkh(ascPacked4dQ, 64'hAAAA_5554_AAAA_AAAA);
    `checkh(ascPacked4dW, 128'hAAAAAAAA_55555554_AAAAAAAA_AAAAAAAA);
`endif

    svCheckContinuousValuesSingleBitReleased();
  endtask

  task automatic vpiCheckSingleBitReleased();
    integer vpiStatus = 1;
`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkSingleBitReleased()");
`else
    vpiStatus = checkSingleBitReleased();
`endif
`elsif IVERILOG
    vpiStatus = $checkSingleBitReleased;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkSingleBitReleased;
`else
    vpiStatus = checkSingleBitReleased();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value after releasing single bit does not match expectation)");
      $stop;
    end
  endtask

    BitIndexingMethod bitIndexingMethod;
    DimIndexingMethod forceDimIndexingMethod;
    DimIndexingMethod releaseDimIndexingMethod;

  initial begin
`ifdef WAVES
$dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
`endif

`ifdef VERILATOR
    vpiPutString();
    vpiTryInvalidPutOperations();
    svReleaseValues(); // Reset any forced values from the invalid put test
    vpiPutInertialDelay();
    #1 vpiCheckInertialDelay();
    // Force and check non-public, but forceable signal
    force nonPublic = 0;
    #8 `checkh(nonPublic, 0);
    release nonPublic;
    #8 `checkh(nonPublic, 1);
`endif

    forceDimIndexingMethod = forceDimIndexingMethod.first();

    // Force through VPI, release through VPI
    if (`verbose) $display("*** Forcing through VPI, releasing through VPI ***");
    do begin
      releaseDimIndexingMethod = releaseDimIndexingMethod.first();
      do begin
        if (`verbose) $display("Forcing with %s, releasing with %s", forceDimIndexingMethod.name(), releaseDimIndexingMethod.name());
        vpiForceValues(forceDimIndexingMethod);
        // Time delay to ensure setting and checking values does not happen
        // at the same time, so that the signals can have their values overwritten
        // by other processes
        #8 vpiCheckValuesForced();
        svCheckValuesForced();
        // Wait until negedge, then release
        @(negedge clk) vpiReleaseValues(releaseDimIndexingMethod);
        // After release, but before posedge: Non-continuously assigned signals
        // should still have their forced value, because the posedge re-assigning
        // the non-continuously assigned signals has not happened yet, but
        // continuously assigned signals should have their non-forced value again
        #1 vpiCheckNonContinuousValuesForced();
        vpiCheckContinuousValuesReleased();
        svCheckNonContinuousValuesForced();
        svCheckContinuousValuesReleased();
        #8;  // All signals should be released by now
        vpiCheckValuesReleased();
        svCheckValuesReleased();

        releaseDimIndexingMethod = releaseDimIndexingMethod.next();
      end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());

      forceDimIndexingMethod = forceDimIndexingMethod.next();
    end while (forceDimIndexingMethod != forceDimIndexingMethod.first());

    // Force through VPI, release through Verilog
    if (`verbose) $display("*** Forcing through VPI, releasing through Verilog ***");
    forceDimIndexingMethod = forceDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Forcing with %s, releasing through Verilog", forceDimIndexingMethod.name());
      #8 vpiForceValues(forceDimIndexingMethod);
      #8 vpiCheckValuesForced();
      svCheckValuesForced();
      @(negedge clk) svReleaseValues();
      #1 vpiCheckNonContinuousValuesForced();
      vpiCheckContinuousValuesReleased();
      svCheckNonContinuousValuesForced();
      svCheckContinuousValuesReleased();
      #8 vpiCheckValuesReleased();
      svCheckValuesReleased();
      forceDimIndexingMethod = forceDimIndexingMethod.next();
    end while (forceDimIndexingMethod != forceDimIndexingMethod.first());

    // Force through Verilog, release through VPI
    if (`verbose) $display("*** Forcing through Verilog, releasing through VPI ***");
    releaseDimIndexingMethod = releaseDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Forcing through Verilog, releasing with %s", releaseDimIndexingMethod.name());
      #8 svForceValues();
      #8 vpiCheckValuesForced();
      svCheckValuesForced();
      @(negedge clk) vpiReleaseValues(releaseDimIndexingMethod);
      #1 vpiCheckNonContinuousValuesForced();
      vpiCheckContinuousValuesReleased();
      svCheckNonContinuousValuesForced();
      svCheckContinuousValuesReleased();
      #8 vpiCheckValuesReleased();
      svCheckValuesReleased();
      releaseDimIndexingMethod = releaseDimIndexingMethod.next();
    end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());

    // Force through Verilog, release through Verilog (but still check value through
    // VPI)
    if (`verbose) $display("*** Forcing through Verilog, releasing through Verilog ***");
    #8 svForceValues();
    #8 vpiCheckValuesForced();
    svCheckValuesForced();
    @(negedge clk) svReleaseValues();
    #1 vpiCheckNonContinuousValuesForced();
    vpiCheckContinuousValuesReleased();
    svCheckNonContinuousValuesForced();
    svCheckContinuousValuesReleased();
    #8 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Partial forcing tests obtain partial handles through
    // vpi_handle_by_name("signalName[hi:lo]", nullptr), which is not
    // supported by Icarus
`ifndef IVERILOG
    // Execute for both ascending and descending bit ranges

    // Descending
    if (`verbose) $display("*** Testing partial forcing with descending bit ranges ***");

    // Partially force through VPI, release through VPI
    if (`verbose) $display("*** Partially forcing through VPI, releasing through VPI ***");
    releaseDimIndexingMethod = releaseDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Partially forcing with through VPI, releasing with %s", releaseDimIndexingMethod.name());
      #8 vpiPartiallyForceValues(Descending);
      #8 vpiCheckValuesPartiallyForced();
      svCheckValuesPartiallyForced();
      @(negedge clk) vpiReleasePartiallyForcedValues(releaseDimIndexingMethod);
      #1 vpiCheckNonContinuousValuesPartiallyForced();
      vpiCheckContinuousValuesReleased();
      svCheckNonContinuousValuesPartiallyForced();
      svCheckContinuousValuesReleased();
      #8 vpiCheckValuesReleased();
      svCheckValuesReleased();
      releaseDimIndexingMethod = releaseDimIndexingMethod.next();
    end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());

    // Partially force through VPI, release through Verilog
    if (`verbose) $display("*** Partially forcing through VPI, releasing through Verilog ***");
    #8 vpiPartiallyForceValues(Descending);
    #8 vpiCheckValuesPartiallyForced();
    svCheckValuesPartiallyForced();
    @(negedge clk) svReleaseValues();
    #1 vpiCheckNonContinuousValuesPartiallyForced();
    vpiCheckContinuousValuesReleased();
    svCheckNonContinuousValuesPartiallyForced();
    svCheckContinuousValuesReleased();
    #8 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Xrun doesn't support ascending bit ranges in vpi_handle_by_name
`ifndef XRUN
    if (`verbose) $display("*** Testing partial forcing with ascending bit ranges ***");

    // Partially force through VPI, release through VPI
    if (`verbose) $display("*** Partially forcing through VPI, releasing through VPI ***");
    releaseDimIndexingMethod = releaseDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Partially forcing through VPI, releasing with %s", releaseDimIndexingMethod.name());
      #8 vpiPartiallyForceValues(Ascending);
      #8 vpiCheckValuesPartiallyForced();
      svCheckValuesPartiallyForced();
      @(negedge clk) vpiReleasePartiallyForcedValues(releaseDimIndexingMethod);
      #1 vpiCheckNonContinuousValuesPartiallyForced();
      vpiCheckContinuousValuesReleased();
      svCheckNonContinuousValuesPartiallyForced();
      svCheckContinuousValuesReleased();
      #8 vpiCheckValuesReleased();
      svCheckValuesReleased();
      releaseDimIndexingMethod = releaseDimIndexingMethod.next();
    end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());

    // Partially force through VPI, release through Verilog
    if (`verbose) $display("*** Partially forcing through VPI, releasing through Verilog ***");
    #8 vpiPartiallyForceValues(Ascending);
    #8 vpiCheckValuesPartiallyForced();
    svCheckValuesPartiallyForced();
    @(negedge clk) svReleaseValues();
    #1 vpiCheckNonContinuousValuesPartiallyForced();
    vpiCheckContinuousValuesReleased();
    svCheckNonContinuousValuesPartiallyForced();
    svCheckContinuousValuesReleased();
    #8 vpiCheckValuesReleased();
    svCheckValuesReleased();
`endif

`endif

    // Partially force through Verilog, release through VPI
    if (`verbose) $display("*** Partially forcing through Verilog, releasing through VPI ***");
    releaseDimIndexingMethod = releaseDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Partially forcing through Verilog, releasing with %s", releaseDimIndexingMethod.name());
      #8 svPartiallyForceValues();
      #8 vpiCheckValuesPartiallyForced();
      svCheckValuesPartiallyForced();
      @(negedge clk) vpiReleasePartiallyForcedValues(releaseDimIndexingMethod);
      #1 vpiCheckNonContinuousValuesPartiallyForced();
      vpiCheckContinuousValuesReleased();
      svCheckNonContinuousValuesPartiallyForced();
      svCheckContinuousValuesReleased();
      #8 vpiCheckValuesReleased();
      svCheckValuesReleased();
      releaseDimIndexingMethod = releaseDimIndexingMethod.next();
    end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());

    // Partially force through Verilog, release through Verilog
    if (`verbose) $display("*** Partially forcing through Verilog, releasing through Verilog ***");
    #8 svPartiallyForceValues();
    #8 vpiCheckValuesPartiallyForced();
    svCheckValuesPartiallyForced();
    @(negedge clk) svReleaseValues();
    #1 vpiCheckNonContinuousValuesPartiallyForced();
    vpiCheckContinuousValuesReleased();
    svCheckNonContinuousValuesPartiallyForced();
    svCheckContinuousValuesReleased();
    #8 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Force through Verilog, partially release through Verilog
    if (`verbose) $display("*** Forcing through Verilog, partially releasing through Verilog ***");
    #8 svForceValues();
    #8 vpiCheckValuesForced();
    svCheckValuesForced();
    @(negedge clk) svPartiallyReleaseValues();
    #1 vpiCheckNonContinuousValuesForced;
    vpiCheckContinuousValuesPartiallyReleased();
    svCheckNonContinuousValuesForced();
    svCheckContinuousValuesPartiallyReleased();
    #8 vpiCheckValuesPartiallyReleased();
    svCheckValuesPartiallyReleased();

`ifndef IVERILOG
    // Execute for both ascending and descending bit ranges

    // Descending
    if (`verbose) $display("*** Testing partial releasing with descending bit ranges ***");

    // Force through VPI, partially release through VPI
    if (`verbose) $display("*** Forcing through VPI, partially releasing through VPI ***");
    forceDimIndexingMethod = forceDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Forcing with %s, partially releasing through VPI", forceDimIndexingMethod.name());
      #8 vpiForceValues(forceDimIndexingMethod);
      #8 vpiCheckValuesForced();
      svCheckValuesForced();
      @(negedge clk) vpiPartiallyReleaseValues(Descending);
      #1 vpiCheckNonContinuousValuesForced();
      vpiCheckContinuousValuesPartiallyReleased();
      svCheckNonContinuousValuesForced();
      svCheckContinuousValuesPartiallyReleased();
      #8 vpiCheckValuesPartiallyReleased();
      svCheckValuesPartiallyReleased();
      forceDimIndexingMethod = forceDimIndexingMethod.next();
    end while (forceDimIndexingMethod != forceDimIndexingMethod.first());

    // Force through Verilog, partially release through VPI
    if (`verbose) $display("*** Forcing through Verilog, partially releasing through VPI ***");
    #8 svForceValues();
    #8 vpiCheckValuesForced();
    svCheckValuesForced();
    @(negedge clk) vpiPartiallyReleaseValues(Descending);
    #1 vpiCheckNonContinuousValuesForced;
    vpiCheckContinuousValuesPartiallyReleased();
    svCheckNonContinuousValuesForced();
    svCheckContinuousValuesPartiallyReleased();
    #8 vpiCheckValuesPartiallyReleased();
    svCheckValuesPartiallyReleased();

    // Ascending
`ifndef XRUN
    if (`verbose) $display("*** Testing partial releasing with ascending bit ranges ***");

    // Force through VPI, partially release through VPI
    if (`verbose) $display("*** Forcing through VPI, partially releasing through VPI ***");
    forceDimIndexingMethod = forceDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Forcing through VPI, partially releasing with %s", forceDimIndexingMethod.name());
      #8 vpiForceValues(forceDimIndexingMethod);
      #8 vpiCheckValuesForced();
      svCheckValuesForced();
      @(negedge clk) vpiPartiallyReleaseValues(Ascending);
      #1 vpiCheckNonContinuousValuesForced;
      vpiCheckContinuousValuesPartiallyReleased();
      svCheckNonContinuousValuesForced();
      svCheckContinuousValuesPartiallyReleased();
      #8 vpiCheckValuesPartiallyReleased();
      svCheckValuesPartiallyReleased();
      forceDimIndexingMethod = forceDimIndexingMethod.next();
    end while (forceDimIndexingMethod != forceDimIndexingMethod.first());

    // Force through Verilog, partially release through VPI
    if (`verbose) $display("*** Forcing through Verilog, partially releasing through VPI ***");
    #8 svForceValues();
    #8 vpiCheckValuesForced();
    svCheckValuesForced();
    @(negedge clk) vpiPartiallyReleaseValues(Ascending);
    #1 vpiCheckNonContinuousValuesForced;
    vpiCheckContinuousValuesPartiallyReleased();
    svCheckNonContinuousValuesForced();
    svCheckContinuousValuesPartiallyReleased();
    #8 vpiCheckValuesPartiallyReleased();
    svCheckValuesPartiallyReleased();

`endif

`endif

    // Force through VPI, partially release through Verilog
    if (`verbose) $display("*** Forcing through VPI, partially releasing through Verilog ***");
    forceDimIndexingMethod = forceDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Forcing with %s, partially releasing through Verilog", forceDimIndexingMethod.name());
      #8 vpiForceValues(forceDimIndexingMethod);
      #8 vpiCheckValuesForced();
      svCheckValuesForced();
      @(negedge clk) svPartiallyReleaseValues();
      #1 vpiCheckNonContinuousValuesForced;
      vpiCheckContinuousValuesPartiallyReleased();
      svCheckNonContinuousValuesForced();
      svCheckContinuousValuesPartiallyReleased();
      #8 vpiCheckValuesPartiallyReleased();
      svCheckValuesPartiallyReleased();
    end while (forceDimIndexingMethod != forceDimIndexingMethod.first());

    // Release everything to reset for next test
    svReleaseValues();
    #8 svCheckValuesReleased();

    // Icarus does not support forcing single bits through VPI
`ifndef IVERILOG
    // Xcelium supports forcing single bits through VPI, but crashes on some signals
`ifndef XRUN

    // Force single bit through VPI, release through VPI
    if (`verbose) $display("*** Forcing single bit through VPI, releasing through VPI ***");
    bitIndexingMethod = bitIndexingMethod.first();
    do begin
      forceDimIndexingMethod = forceDimIndexingMethod.first();
      do begin
        releaseDimIndexingMethod = releaseDimIndexingMethod.first();
        do begin
          if (`verbose) $display("Forcing single bit with bit indexing method %s and dimension indexing method %s, releasing with dimension indexing method %s", bitIndexingMethod.name(), forceDimIndexingMethod.name(), releaseDimIndexingMethod.name());
          #8 vpiForceSingleBit(bitIndexingMethod, forceDimIndexingMethod);
          #8 vpiCheckSingleBitForced();
          svCheckSingleBitForced();
          @(negedge clk) vpiReleaseSingleBitForcedValues(releaseDimIndexingMethod);
          #1 vpiCheckNonContinuousSingleBitForced();
          vpiCheckContinuousValuesReleased();
          svCheckNonContinuousSingleBitForced();
          svCheckContinuousValuesReleased();
          #8 vpiCheckValuesReleased();
          svCheckValuesReleased();
          releaseDimIndexingMethod = releaseDimIndexingMethod.next();
        end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());
        forceDimIndexingMethod = forceDimIndexingMethod.next();
      end while (forceDimIndexingMethod != forceDimIndexingMethod.first());
      bitIndexingMethod = bitIndexingMethod.next();
    end while (bitIndexingMethod != bitIndexingMethod.first());

    // Force single bit through VPI, release through Verilog
    if (`verbose) $display("*** Forcing single bit through VPI, releasing through Verilog ***");
    bitIndexingMethod = bitIndexingMethod.first();
    do begin
      forceDimIndexingMethod = forceDimIndexingMethod.first();
      do begin
        if (`verbose) $display("Forcing single bit with bit indexing method %s and dimension indexing method %s, releasing through Verilog", bitIndexingMethod.name(), forceDimIndexingMethod.name());
        #8 vpiForceSingleBit(bitIndexingMethod, forceDimIndexingMethod);
        #8 vpiCheckSingleBitForced();
        svCheckSingleBitForced();
        @(negedge clk) svReleaseValues();
        #1 vpiCheckNonContinuousSingleBitForced();
        vpiCheckContinuousValuesReleased();
        svCheckNonContinuousSingleBitForced();
        svCheckContinuousValuesReleased();
        #8 vpiCheckValuesReleased();
        svCheckValuesReleased();
        forceDimIndexingMethod = forceDimIndexingMethod.next();
      end while (forceDimIndexingMethod != forceDimIndexingMethod.first());
      bitIndexingMethod = bitIndexingMethod.next();
    end while (bitIndexingMethod != bitIndexingMethod.first());

    // Force single bit through Verilog, release through VPI
    if (`verbose) $display("*** Forcing single bit through Verilog, releasing through VPI ***");
    releaseDimIndexingMethod = releaseDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Forcing single bit through Verilog, releasing with %s", releaseDimIndexingMethod.name());
      #8 svForceSingleBit();
      #8 vpiCheckSingleBitForced();
      svCheckSingleBitForced();
      @(negedge clk) vpiReleaseSingleBitForcedValues(releaseDimIndexingMethod);
      #1 vpiCheckNonContinuousSingleBitForced();
      vpiCheckContinuousValuesReleased();
      svCheckNonContinuousSingleBitForced();
      svCheckContinuousValuesReleased();
      #8 vpiCheckValuesReleased();
      svCheckValuesReleased();
      releaseDimIndexingMethod = releaseDimIndexingMethod.next();
    end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());

    // Force single bit through Verilog, release through Verilog
    if (`verbose) $display("*** Forcing single bit through Verilog, releasing through Verilog ***");
    #8 svForceSingleBit();
    #8 vpiCheckSingleBitForced();
    svCheckSingleBitForced();
    @(negedge clk) svReleaseValues();
    #1 vpiCheckNonContinuousSingleBitForced();
    vpiCheckContinuousValuesReleased();
    svCheckNonContinuousSingleBitForced();
    svCheckContinuousValuesReleased();
    #8 vpiCheckValuesReleased();
    svCheckValuesReleased();

    // Force through VPI, release single bit through VPI
    if (`verbose) $display("*** Forcing through VPI, releasing single bit through VPI ***");
    bitIndexingMethod = bitIndexingMethod.first();
    do begin
      forceDimIndexingMethod = forceDimIndexingMethod.first();
      do begin
        releaseDimIndexingMethod = releaseDimIndexingMethod.first();
        do begin
          if (`verbose) $display("Forcing with %s, releasing single bit with bit indexing method %s and dimension indexing method %s", forceDimIndexingMethod.name(), bitIndexingMethod.name(), releaseDimIndexingMethod.name());
          #8 vpiForceValues(forceDimIndexingMethod);
          #8 vpiCheckValuesForced();
          svCheckValuesForced();
          @(negedge clk) vpiReleaseSingleBit(bitIndexingMethod, releaseDimIndexingMethod);
          #1 vpiCheckNonContinuousValuesForced();
          vpiCheckContinuousValuesSingleBitReleased();
          svCheckNonContinuousValuesForced();
          svCheckContinuousValuesSingleBitReleased();
          #8 vpiCheckSingleBitReleased();
          svCheckSingleBitReleased();
          releaseDimIndexingMethod = releaseDimIndexingMethod.next();
        end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());
        forceDimIndexingMethod = forceDimIndexingMethod.next();
      end while (forceDimIndexingMethod != forceDimIndexingMethod.first());
      bitIndexingMethod = bitIndexingMethod.next();
    end while (bitIndexingMethod != bitIndexingMethod.first());

    // Force through VPI, release single bit through Verilog
    if (`verbose) $display("*** Forcing through VPI, releasing single bit through Verilog ***");
    forceDimIndexingMethod = forceDimIndexingMethod.first();
    do begin
      if (`verbose) $display("Forcing with %s, releasing single bit through Verilog", forceDimIndexingMethod.name());
      #8 vpiForceValues(forceDimIndexingMethod);
      #8 vpiCheckValuesForced();
      svCheckValuesForced();
      @(negedge clk) svReleaseSingleBit();
      #1 vpiCheckNonContinuousValuesForced();
      vpiCheckContinuousValuesSingleBitReleased();
      svCheckNonContinuousValuesForced();
      svCheckContinuousValuesSingleBitReleased();
      #8 vpiCheckSingleBitReleased();
      svCheckSingleBitReleased();
      forceDimIndexingMethod = forceDimIndexingMethod.next();
    end while (forceDimIndexingMethod != forceDimIndexingMethod.first());

    // Force through Verilog, release single bit through VPI
    if (`verbose) $display("*** Forcing through Verilog, releasing single bit through VPI ***");
    bitIndexingMethod = bitIndexingMethod.first();
    do begin
      releaseDimIndexingMethod = releaseDimIndexingMethod.first();
      do begin
        if (`verbose) $display("Forcing through Verilog, releasing single bit with bit indexing method %s and dimension indexing method %s", bitIndexingMethod.name(), releaseDimIndexingMethod.name());
        #8 svForceValues();
        #8 vpiCheckValuesForced();
        svCheckValuesForced();
        @(negedge clk) vpiReleaseSingleBit(bitIndexingMethod, releaseDimIndexingMethod);
        #1 vpiCheckNonContinuousValuesForced();
        vpiCheckContinuousValuesSingleBitReleased();
        svCheckNonContinuousValuesForced();
        svCheckContinuousValuesSingleBitReleased();
        #8 vpiCheckSingleBitReleased();
        svCheckSingleBitReleased();
        releaseDimIndexingMethod = releaseDimIndexingMethod.next();
      end while (releaseDimIndexingMethod != releaseDimIndexingMethod.first());
      bitIndexingMethod = bitIndexingMethod.next();
    end while (bitIndexingMethod != bitIndexingMethod.first());

    // Force through Verilog, release single bit through Verilog
    if (`verbose) $display("*** Forcing through Verilog, releasing single bit through Verilog ***");
    #8 svForceValues();
    #8 vpiCheckValuesForced();
    svCheckValuesForced();
    @(negedge clk) svReleaseSingleBit();
    #1 vpiCheckNonContinuousValuesForced();
    vpiCheckContinuousValuesSingleBitReleased();
    svCheckNonContinuousValuesForced();
    svCheckContinuousValuesSingleBitReleased();
    #8 vpiCheckSingleBitReleased();
    svCheckSingleBitReleased();
`endif
`endif

    #5 $display("*-* All Finished *-*");
    $finish;
  end

`ifdef TEST_VERBOSE
  always @(posedge clk or negedge clk) begin
    $display("time: %0t\tclk:%b", $time, clk);

    $display("nonPublic: %x", nonPublic);

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

    $display("packed2dC: %x", packed2dC);
    $display("packed2dS: %x", packed2dS);
    $display("packed2dI: %x", packed2dI);
    $display("packed2dQ: %x", packed2dQ);
    $display("packed2dW: %x", packed2dW);
    $display("packed3dS: %x", packed3dS);
    $display("packed3dI: %x", packed3dI);
    $display("packed3dQ: %x", packed3dQ);
    $display("packed3dW: %x", packed3dW);
    $display("packed4dC: %x", packed4dC);
    $display("packed4dS: %x", packed4dS);
    $display("packed4dI: %x", packed4dI);
    $display("packed4dQ: %x", packed4dQ);
    $display("packed4dW: %x", packed4dW);
    $display("ascPacked4dC: %x", ascPacked4dC);
    $display("ascPacked4dS: %x", ascPacked4dS);
    $display("ascPacked4dI: %x", ascPacked4dI);
    $display("ascPacked4dQ: %x", ascPacked4dQ);
    $display("ascPacked4dW: %x", ascPacked4dW);

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

    $display("packed2dCContinuously: %x", packed2dCContinuously);
    $display("packed2dSContinuously: %x", packed2dSContinuously);
    $display("packed2dIContinuously: %x", packed2dIContinuously);
    $display("packed2dQContinuously: %x", packed2dQContinuously);
    $display("packed2dWContinuously: %x", packed2dWContinuously);
    $display("packed3dSContinuously: %x", packed3dSContinuously);
    $display("packed3dIContinuously: %x", packed3dIContinuously);
    $display("packed3dQContinuously: %x", packed3dQContinuously);
    $display("packed3dWContinuously: %x", packed3dWContinuously);
    $display("packed4dCContinuously: %x", packed4dCContinuously);
    $display("packed4dSContinuously: %x", packed4dSContinuously);
    $display("packed4dIContinuously: %x", packed4dIContinuously);
    $display("packed4dQContinuously: %x", packed4dQContinuously);
    $display("packed4dWContinuously: %x", packed4dWContinuously);
    $display("ascPacked4dCContinuously: %x", ascPacked4dCContinuously);
    $display("ascPacked4dSContinuously: %x", ascPacked4dSContinuously);
    $display("ascPacked4dIContinuously: %x", ascPacked4dIContinuously);
    $display("ascPacked4dQContinuously: %x", ascPacked4dQContinuously);
    $display("ascPacked4dWContinuously: %x", ascPacked4dWContinuously);

    $display("========================\n");
  end
`endif

endmodule
