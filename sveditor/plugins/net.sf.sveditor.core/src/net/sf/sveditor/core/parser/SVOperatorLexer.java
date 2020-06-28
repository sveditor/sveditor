/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.scanutils.ITextScanner;

class SVOperatorLexer implements ISVOperators {
  static OP operator(ITextScanner scanner) throws SVParseException {
    int ch = scanner.get_ch();
    OP op = null;

    switch (ch) {
// OPS: != !== !=? 
      case '!': {
        int c1 = scanner.get_ch();
// OPS: !== !=? 
          if (c1 == '=') {
            int c2 = scanner.get_ch();
              if (c2 == '=') {
                op = OP.NOT_EQ2;
              } else if (c2 == '?') {
                op = OP.NOT_EQ_TERN;
              } else {
                op = OP.NOT_EQ;
                scanner.unget_ch(c2);
              }
          } else {
            op = OP.NOT;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: ## #-# #=# 
      case '#': {
        int c1 = scanner.get_ch();
          if (c1 == '#') {
            op = OP.HASH2;
          } else if (c1 == '-') {
            scanner.get_ch();
            op = OP.HASH_SUB_HASH;
          } else if (c1 == '=') {
            scanner.get_ch();
            op = OP.HASH_EQ_HASH;
          } else {
            op = OP.HASH;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case '$': {
        op = OP.DOLLAR;
        } break;
// OPS: %= 
      case '%': {
        int c1 = scanner.get_ch();
          if (c1 == '=') {
            op = OP.MOD_EQ;
          } else {
            op = OP.MOD;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: && &&& &= 
      case '&': {
        int c1 = scanner.get_ch();
// OPS: &&& 
          if (c1 == '&') {
            int c2 = scanner.get_ch();
              if (c2 == '&') {
                op = OP.AND3;
              } else {
                op = OP.AND2;
                scanner.unget_ch(c2);
              }
          } else if (c1 == '=') {
            op = OP.AND_EQ;
          } else {
            op = OP.AND;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case '\'': {
        op = OP.SQUOTE;
        } break;
// OPS: (* 
      case '(': {
        int c1 = scanner.get_ch();
          if (c1 == '*') {
            op = OP.LPAREN_MUL;
          } else {
            op = OP.LPAREN;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case ')': {
        op = OP.RPAREN;
        } break;
// OPS: *) ** *= *> 
      case '*': {
        int c1 = scanner.get_ch();
          if (c1 == ')') {
            op = OP.MUL_RPAREN;
          } else if (c1 == '*') {
            op = OP.MUL2;
          } else if (c1 == '=') {
            op = OP.MUL_EQ;
          } else if (c1 == '>') {
            op = OP.MUL_GT;
          } else {
            op = OP.MUL;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: +*> ++ +: += +=> 
      case '+': {
        int c1 = scanner.get_ch();
          if (c1 == '*') {
            scanner.get_ch();
            op = OP.PLUS_MUL_GT;
          } else if (c1 == '+') {
            op = OP.INC;
          } else if (c1 == ':') {
            op = OP.PLUS_COLON;
// OPS: +=> 
          } else if (c1 == '=') {
            int c2 = scanner.get_ch();
              if (c2 == '>') {
                op = OP.PLUS_GE;
              } else {
                op = OP.PLUS_EQ;
                scanner.unget_ch(c2);
              }
          } else {
            op = OP.PLUS;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case ',': {
        op = OP.COMMA;
        } break;
// OPS: -*> -- --> -: -= -=> -> ->> 
      case '-': {
        int c1 = scanner.get_ch();
          if (c1 == '*') {
            scanner.get_ch();
            op = OP.SUB_MUL_GT;
// OPS: --> 
          } else if (c1 == '-') {
            int c2 = scanner.get_ch();
              if (c2 == '>') {
                op = OP.IMPL2;
              } else {
                op = OP.DEC;
                scanner.unget_ch(c2);
              }
          } else if (c1 == ':') {
            op = OP.SUB_COLON;
// OPS: -=> 
          } else if (c1 == '=') {
            int c2 = scanner.get_ch();
              if (c2 == '>') {
                op = OP.SUB_GE;
              } else {
                op = OP.SUB_EQ;
                scanner.unget_ch(c2);
              }
// OPS: ->> 
          } else if (c1 == '>') {
            int c2 = scanner.get_ch();
              if (c2 == '>') {
                op = OP.IMPL_RSHIFT;
              } else {
                op = OP.IMPL;
                scanner.unget_ch(c2);
              }
          } else {
            op = OP.MINUS;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: .* 
      case '.': {
        int c1 = scanner.get_ch();
          if (c1 == '*') {
            op = OP.DOT_MUL;
          } else {
            op = OP.DOT;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: /= 
      case '/': {
        int c1 = scanner.get_ch();
          if (c1 == '=') {
            op = OP.DIV_EQ;
          } else {
            op = OP.DIV;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: :/ :: := 
      case ':': {
        int c1 = scanner.get_ch();
          if (c1 == '/') {
            op = OP.COLON_DIV;
          } else if (c1 == ':') {
            op = OP.COLON2;
          } else if (c1 == '=') {
            op = OP.COLON_EQ;
          } else {
            op = OP.COLON;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case ';': {
        op = OP.SEMICOLON;
        } break;
// OPS: <+ << <<< <<<= <<= <= 
      case '<': {
        int c1 = scanner.get_ch();
          if (c1 == '+') {
            op = OP.LT_PLUS;
// OPS: <<< <<<= <<= 
          } else if (c1 == '<') {
            int c2 = scanner.get_ch();
// OPS: <<<= 
              if (c2 == '<') {
                int c3 = scanner.get_ch();
                  if (c3 == '=') {
                    op = OP.LSHIFT3_EQ;
                  } else {
                    op = OP.LSHIFT3;
                    scanner.unget_ch(c3);
                  }
              } else if (c2 == '=') {
                op = OP.LSHIFT_EQ;
              } else {
                op = OP.LSHIFT;
                scanner.unget_ch(c2);
              }
          } else if (c1 == '=') {
            op = OP.LE;
          } else {
            op = OP.LT;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: == === ==? => 
      case '=': {
        int c1 = scanner.get_ch();
// OPS: === ==? 
          if (c1 == '=') {
            int c2 = scanner.get_ch();
              if (c2 == '=') {
                op = OP.EQ3;
              } else if (c2 == '?') {
                op = OP.EQ2_TERN;
              } else {
                op = OP.EQ2;
                scanner.unget_ch(c2);
              }
          } else if (c1 == '>') {
            op = OP.EQ_GT;
          } else {
            op = OP.EQ;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: >= >> >>= >>> >>>= 
      case '>': {
        int c1 = scanner.get_ch();
          if (c1 == '=') {
            op = OP.GE;
// OPS: >>= >>> >>>= 
          } else if (c1 == '>') {
            int c2 = scanner.get_ch();
              if (c2 == '=') {
                op = OP.RSHIFT_EQ;
// OPS: >>>= 
              } else if (c2 == '>') {
                int c3 = scanner.get_ch();
                  if (c3 == '=') {
                    op = OP.RSHIFT3_EQ;
                  } else {
                    op = OP.RSHIFT3;
                    scanner.unget_ch(c3);
                  }
              } else {
                op = OP.RSHIFT;
                scanner.unget_ch(c2);
              }
          } else {
            op = OP.GT;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case '?': {
        op = OP.TERNARY;
        } break;
// OPS: @@ 
      case '@': {
        int c1 = scanner.get_ch();
          if (c1 == '@') {
            op = OP.AT2;
          } else {
            op = OP.AT;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case '[': {
        op = OP.LBRACKET;
        } break;
// OPS: 
      case ']': {
        op = OP.RBRACKET;
        } break;
// OPS: ^= ^~ 
      case '^': {
        int c1 = scanner.get_ch();
          if (c1 == '=') {
            op = OP.XOR_EQ;
          } else if (c1 == '~') {
            op = OP.XOR_NEG;
          } else {
            op = OP.XOR;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case '{': {
        op = OP.LBRACE;
        } break;
// OPS: |-> |= |=> || 
      case '|': {
        int c1 = scanner.get_ch();
          if (c1 == '-') {
            scanner.get_ch();
            op = OP.OR_IMPL;
// OPS: |=> 
          } else if (c1 == '=') {
            int c2 = scanner.get_ch();
              if (c2 == '>') {
                op = OP.OR_EQ_GT;
              } else {
                op = OP.OR_EQ;
                scanner.unget_ch(c2);
              }
          } else if (c1 == '|') {
            op = OP.OR2;
          } else {
            op = OP.OR;
            scanner.unget_ch(c1);
          }
        } break;
// OPS: 
      case '}': {
        op = OP.RBRACE;
        } break;
// OPS: ~& ~^ ~| 
      case '~': {
        int c1 = scanner.get_ch();
          if (c1 == '&') {
            op = OP.NEG_AND;
          } else if (c1 == '^') {
            op = OP.NEG_XOR;
          } else if (c1 == '|') {
            op = OP.NEG_OR;
          } else {
            op = OP.NEG;
            scanner.unget_ch(c1);
          }
        } break;
    }
    return op;
  }
}
