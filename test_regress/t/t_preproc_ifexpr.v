// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`begin_keywords "1800-2023"

`define ONE
`undef ZERO

`ifdef ( ONE )
  "ok  ( ONE )"
`endif
// Test no spaces around ()
`ifdef (ZERO)
 `error "( ZERO )"
`endif

`ifndef ( ! ONE )
  "ok   ( ! ONE )"
`endif
// Test no spaces around ()
`ifndef (!ZERO)
 `error "( ! ZERO )"
`endif

`ifdef ( ! ZERO )
  "ok  ( ! ZERO )"
`endif
`ifdef ( ! ONE )
 `error "( ! ONE )"
`endif

`ifdef ( ZERO || ZERO || ONE )
  "ok  ( ZERO || ZERO || ONE )"
`endif
`ifdef ( ZERO || ZERO || ZERO )
  `error "( ZERO || ZERO || ZERO )"
`endif

`ifdef ( ONE && ONE && ONE )
  "ok  ( ONE && ONE && ONE )"
`endif
`ifdef ( ONE && ONE && ZERO )
  `error "( ONE && ONE && ZERO )"
`endif

// Precedence of && is under ||

`ifdef ( ZERO && ZERO || ONE )
  "ok  ( ZERO && ZERO || ONE )"
`endif
`ifdef ( ONE || ZERO && ZERO )
  "ok  ( ONE || ZERO && ZERO )"
`endif

`ifdef ZERO
`elsif ( ONE && !( ZERO && ONE ) )
  "ok  ( ONE && !( ZERO && ONE ) )"
`endif

`ifdef ( ZERO -> ZERO)
  "ok  ( ZERO -> ZERO)"
`endif

// Text extra newlines
`ifdef ( ZERO
         ->
         ONE)
  "ok  ( ZERO -> ONE)"
`endif

// Text comments
`ifdef ( ZERO  // Zero
         ->    // Operator
         ONE)  // One
  "ok  ( ZERO -> ONE)"
`endif
`ifdef ( /*val*/ ZERO
         /*op*/ ->
         /*val*/ ONE)
  "ok  ( ZERO -> ONE)"
`endif

`ifndef ( ONE -> ZERO)
  "ok  ( ONE -> ZERO)"
`endif
`ifdef ( ONE -> ONE)
  "ok  ( ONE -> ONE)"
`endif

`ifdef ( ZERO <-> ZERO)
  "ok  ( ZERO <-> ZERO)"
`endif
`ifndef ( ZERO <-> ONE)
  "ok  ( ZERO <-> ONE)"
`endif
`ifndef ( ONE <-> ZERO)
  "ok  ( ONE <-> ZERO)"
`endif
`ifdef ( ONE <-> ONE)
  "ok  ( ONE <-> ONE)"
`endif

`ifdef (ZERO)
  "bad"
`elsif (ZERO)
  "bad"
`elsif (ONE)
  "ok "
`elsif (ONE)
  "bad"
`endif

// Did we end up right?
Line: `__LINE__
