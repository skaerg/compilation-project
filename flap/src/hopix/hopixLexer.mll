(** Prelude *)
{ (* -*- tuareg -*- *)
  open Lexing
  open Error
  open Position
  open HopixParser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "during lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)

  (* convert parsed string to char:
   * ascii => ex: "'\\077'" : len=6 (escaped char counts for 1 + don't forget the quotes) => ret 'M'
   * hex => ex: "'\\0x4b'" : len=7 => ret 'K'
   * printable => ex: "'a'" : len=3 => ret 'a'
   * escaped => ex: "'\\t'" : len=4 => ret '\t'
  *)
  let to_char c =
  match (String.length c) with
   | 3 -> String.get c 1
   | 4 -> String.get (Scanf.unescaped (String.sub c 1 2)) 0
   | 6 -> Char.chr (int_of_string (String.sub c 2 3))
   | 7 -> Char.chr (int_of_string (String.sub c 2 4))
   | _ -> raise (Failure "Invalid char length.")
}

(** Declarations *)
let newline = ('\010' | '\013' | "\013\010")
let blank   = [' ' '\009' '\012']

let digit = ['0'-'9']
let binary = "0b" ( '0' | '1' )+
let octal = "0o" ['0' - '7']+

let atof_lower = ['a' - 'f']
let atof_upper = ['A' - 'F']
let hexadecimal = "0x" (digit | atof_lower | atof_upper)+

let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']

let constr_id = uppercase (uppercase | lowercase | digit | '_')*
let lowercase_id = lowercase (uppercase | lowercase | digit | '_')*
let type_variable = '`' lowercase_id
let int = ('-'? digit+) | hexadecimal | binary | octal

(** an ascii character \xyz matches:
  *   | x=0|1 and y=(0 to 9) and z=(0 to 9)
  *   | x=2   and y=(0 to 5) and z=(0 to 5)
  * 
  * a printable character (see https://theasciicode.com.ar/)
  * ranges from SPACE to TILDE, including SINGLEQUOTE
  * and DOUBLEQUOTE
  *)
let ascii = '\\' digit digit digit
let hex = "\\0x" ['0'-'9' 'a'-'f' 'A'-'F']['0'-'9' 'a'-'f' 'A'-'F']
let printable_no_quotes = [' '-'!' '#'-'&' '('-'~'] (* printable, excluding single and double quotes *)
let escaped = '\\''\\' | "\\""'" | '\\''n' | '\\''t' | '\\''b' | '\\''r'
let atom_no_dq = ascii | hex | printable_no_quotes | escaped (* atom, excluding doublequotes *)
let char = "'" (atom_no_dq | '"') "'"
let bad_ascii_char = "'" ('\\' ('2'['6'-'9']['6'-'9'] | ['3'-'9']['0'-'9']['0'-'9'])) "'"


(** Main rule *)
rule token = parse
  
  (** Layout *)
  | newline               { next_line_and token lexbuf           }
  | blank+                { token lexbuf                         }
  | eof                   { EOF                                  }

  (** Comments *)
  | "##"                  { oneline_comment lexbuf               }
  | "{*"                  { multiline_comment 1 lexbuf           }

  (** Keywords *)
  | "and"                 { AND                                  }
  | "do"                  { DO                                   }
  | "else"                { ELSE                                 }
  | "extern"              { EXTERN                               }
  | "for"                 { FOR                                  }
  | "from"                { FROM                                 }
  | "fun"                 { FUN                                  }
  | "if"                  { IF                                   }
  | "let"                 { LET                                  }
  | "match"               { MATCH                                }
  | "ref"                 { REF                                  }
  | "then"                { THEN                                 }
  | "to"                  { TO                                   }
  | "type"                { TYPE                                 }
  | "until"               { UNTIL                                }
  | "while"               { WHILE                                }
  
  (** Punctuation and binary operators *)
  | "="                   { EQUAL                                }
  | "->"                  { ARROW                                }
  | "<"                   { LANGLE                               }
  | ">"                   { RANGLE                               }
  | "("                   { LPAREN                               }
  | ")"                   { RPAREN                               }
  | '{'                   { LCURLY                               }
  | '}'                   { RCURLY                               }
  | '['                   { LSQUARE                              }
  | ']'                   { RSQUARE                              }
  | '|'                   { BAR                                  }
  | '&'                   { AMPERSAND                            }
  | ":"                   { COLON                                }
  | ";"                   { SEMICOLON                            }
  | ","                   { COMMA                                }
  | "!"                   { EMARK                                }
  | '+'                   { PLUS                                 }
  | '-'                   { MINUS                                }
  | '*'                   { STAR                                 }
  | '/'                   { SLASH                                }
  | "\\"                  { BACKSLASH                            }
  | '_'                   { UNDERSCORE                           }
  | '.'                   { DOT                                  }
  | ":="                  { ASSIGN                               }
  | "&&"                  { LOGICAL_AND                          }
  | "||"                  { LOGICAL_OR                           }
  | "=?"                  { EQUAL_TEST                           }
  | "<=?"                 { LESS_OR_EQ_TEST                      }
  | ">=?"                 { GREATER_OR_EQ_TEST                   }
  | "<?"                  { LESS_TEST                            }
  | ">?"                  { GREATER_TEST                         }
  
  (** Identifiers *)
  | type_variable as s    { TYPE_VARIABLE s                      }
  | constr_id as s        { CONSTR_ID s                          }
  | lowercase_id as s     { LOWERCASE_ID s                       }

  (** LITERALS *)
  | int as i              { INT (Mint.of_string i)               }
  | char as c             
    { 
      try (CHAR (to_char c))
      with e -> (Error.error "during lexing" (Position.cpos lexbuf) "")
    }
  | '"'                   { STRING (string "" lexbuf)            }

  (** Lexing error *)
  | _                     { error lexbuf "unexpected character." }



(** String rule
  * returning the str as is may be incorrect when escape sequences
  * are present (ex: "hi\\n" => "hi\n")
  * c.f. https://medium.com/@huund/recipes-for-ocamllex-bb4efa0afe53
  * § Scanning Complex Tokens Like Strings
  * but instead of using a buffer as the entrypoint param, we use an
  * initially empty string + we use the to_char function we wrote
  * above instead of matching every char of the str
  *)
and string s = parse
  | (atom_no_dq | "'") as c { let s = s^(String.make 1 (to_char ("'"^c^"'")))
                              in string s lexbuf                  }
  | '\\''\"'                { string (s^"\"") lexbuf              }
  | '"'                     { s                                   }
  | eof                     { error lexbuf "Unterminated string." }
  | _                       { error lexbuf "Unterminated string." }



(** One line comment rule *)

and oneline_comment = parse
  | newline                 { next_line_and token lexbuf }
  | eof                     { EOF                        }
  | _                       { oneline_comment lexbuf     }


(** Multiline comment rule *)

and multiline_comment nesting_level = parse
  | eof { error lexbuf "Unterminated comment."                       }
  | "{*" { multiline_comment (nesting_level+1) lexbuf                }
  | "*}" { match nesting_level with
            | 1 -> token lexbuf
            | _ -> multiline_comment (nesting_level-1) lexbuf        }
  | newline { next_line_and (multiline_comment nesting_level) lexbuf }
  | _ { multiline_comment nesting_level lexbuf                       }