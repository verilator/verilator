---
name: verilator-parser
description: Lexer/grammar specifics - token pipeline, precedence, //UNSUP, error recovery, verilog.y/verilog.l
---

# Verilator Parser Skill

## Lexer/Parser Overview

| File | Purpose |
|------|---------|
| `verilog.l` | Lexer (Flex) - tokens, keywords, numbers, strings |
| `verilog.y` | Grammar (Bison) - productions, precedence, AST node creation |

## Token Pipeline

```
Source text -> verilog.l (Flex) -> tokens -> verilog.y (Bison) -> AST
```

Key points:
- **No preprocessor in lexer** - `v3pp` runs first, lexer sees expanded text
- **Token names** follow pattern: `K_<KEYWORD>`, `TK_<TYPE>`, `SYM_<SYMBOL>`
- **Line/column** tracked via `yylineno`, `yycolumn`

## Adding New Keyword/Token

1. **verilog.l** - add token definition:
```flex
"newkeyword"    { return K_NEWKEYWORD; }
```

2. **verilog.y** - add to `%token` section:
```bison
%token K_NEWKEYWORD
```

3. **verilog.y** - use in grammar rule:
```bison
new_construct:
    K_NEWKEYWORD expression
    { $$ = new AstNewConstruct{@$, $2}; }
```

4. **V3AstNode*.h** - declare new AST node with `@astgen`
5. **V3Ast.cpp** - implement `dump()`, `dumpJson()`, `isSame()`, `cloneRelink()`

## Precedence & Associativity

Defined in `verilog.y` `%left`/`%right`/`%nonassoc` sections:

```bison
%left  OR_OP          // ||
%left  AND_OP         // &&
%left  EQ_OP NE_OP    // == !=
%left  LT_OP LE_OP GT_OP GE_OP  // < <= > >=
%left  SHIFT_OP       // << >>
%left  PLUS_MINUS     // + -
%left  MUL_DIV_MOD    // * / %
%right UNARY_OP       // ! ~ + - $signed $unsigned
%right POW_OP         // **
```

**Rule**: When adding operators, place in correct precedence level.

## //UNSUP - Unsupported Features

For features not yet implemented:

```bison
unsupported_feature:
    K_UNSUPPORTED_KW  { v3error("Unsupported: %0", "feature name"); $$ = AstConst::BitFalse; }
```

- Use `v3error("Unsupported: ...")` NOT `v3error("Error: ...")`
- Test goes in `t_*_unsup.v` + `.py`
- When feature lands, REMOVE from unsup test in SAME commit

## Error Recovery

```bison
// Error recovery rule - skip to next statement
statement_list:
    statement_list error ';'
    { /* skip bad statement */ }
```

- Add `error` productions for recovery points
- Don't suppress errors - let them surface with context

## Token Look-ahead

For ambiguities, use `tokenPipeScan*`:

```cpp
// In grammar action - peek ahead
if (tokenPipeScan(0, K_XOR)) { ... }
```

Available: `tokenPipeScan`, `tokenPipePeek`, `tokenPipeGet`

## Parser Testing

```systemverilog
// test_regress/t/t_parse_<feature>.v
module t;
    // Test grammar rule
endmodule
```

```python
# test_regress/t/t_parse_<feature>.py
import vltest_bootstrap
test.lint()  # Parse only
test.passes()
```

## Common Patterns

| Pattern | Implementation |
|---------|----------------|
| Optional clause | `opt_clause: %empty | clause` |
| Comma-separated list | `list: item | list ',' item` |
| Hierarchical path | `path: identifier ('.' identifier)*` |
| Packed/unpacked dims | `dims: '[' expr ']' dims | %empty` |

## Token Efficiency

- **Don't read full grammar** - search for specific rule: `grep -n "rule_name" verilog.y`
- **Modify in place** - add to existing precedence/associativity
- **Test each | branch** - every alternative needs a test case