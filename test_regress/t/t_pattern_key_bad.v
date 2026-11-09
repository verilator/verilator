// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int k = 1;

  initial begin
    // An array pattern key must be a constant expression (IEEE 1800-2023 10.9)
    automatic int dict[int] = '{k: 5};
    automatic int dict2[int] = '{k + 1: 6};
    automatic int wild[*] = '{k: 7};
    automatic int wild2[*] = '{k + 1: 8};
    automatic int wild3[*] = '{9};
    $display("%p %p %p %p %p", dict, dict2, wild, wild2, wild3);
    $stop;
  end

  // A dynamic array or queue pattern is sized by its largest index key, so needs one. Each
  // element also needs a key or the default, as there is no new[]
  int d[] = '{3: 10};
  int q[$] = '{0: 11, 2: 12};
  int qdup[$] = '{1: 15, 2: 16, 1: 17};
  int dd[] = '{default: 23};
  int qd[$] = '{default: 24};
  int qgaps[$] = '{1: 18, 4: 19, 6: 20};
  int dn[] = '{-1: 13, default: 0};
  int qn[$] = '{-1: 27, default: 0};
  int dbig[] = '{32'h8000_0000: 28, default: 0};
  int qbig[$] = '{64'h8000_0000: 14, default: 0};
  int qmax[$] = '{32'h7fff_ffff: 25, default: 0};
  int qwide[$] = '{65'h1_0000_0000_0000_0000: 21, default: 0};
  int qu64[$] = '{64'hffff_ffff_ffff_ffff: 22, default: 0};
  int qneg[$] = '{65'sh1_0000_0000_0000_0005: 26, default: 0};

  // Values are checked against the element type, as positional ones are
  typedef struct {int a;} v_t;
  v_t sv;
  int qs[$] = '{0: sv};
  int qsd[$] = '{0: 1, default: sv};
  int as[int] = '{0: sv};
  int asd[int] = '{default: sv};
  int ws[*] = '{"a": sv};
  int wsd[*] = '{default: sv};

  // The keys of a new[] initializer are checked the same way
  initial begin
    d = new[4] ('{k: 28});
    d = new[4] ('{1: 29, 2: 30, 1: 31});
    d = new[4] ('{2'bx1: 32, default: 0});
    d = new[4] ('{-1: 33});
    d = new[4] ('{64'h1_0000_0001: 34});
    d = new[4] ('{65'h1_0000_0000_0000_0001: 35});
    d = new[4] ('{65'sh1_0000_0000_0000_0002: 36});
    d = new[4] ('{64'hffff_ffff_ffff_fff0: 37, 64'hffff_ffff_ffff_fff1: 38});
  end

  // Keys must be unique (IEEE 1800-2023 10.9.1), after conversion to the key type
  int dup[int] = '{1: 14, 2: 15, 1: 16};
  int trip[int] = '{1: 17, 2: 18, 1: 19, 1: 20};
  int wdup[*] = '{"CCC": 21, 23'h434343: 22};

  // A key containing X or Z is an invalid index (IEEE 1800-2023 7.4.5, 7.8.1, 7.8.4), even where
  // converting it to the key type would drop them. Rejected, rather than ignored with a warning.
  int xun[2] = '{2'bx1: 25, default: 0};
  int xwild[*] = '{4'b10x1: 26};
  int xlogic[logic [3:0]] = '{4'bx: 27};
  int xint[int] = '{4'bx: 28};
  int xtrunc[logic [1:0]] = '{4'bx001: 29};

  // Struct keys are checked the same way
  typedef struct {
    int a;
    logic [3:0] b;
  } s_t;
  int snonconst[s_t] = '{'{k, 1} : 30};
  int sx[s_t] = '{'{1, 4'bx} : 31};

endmodule
