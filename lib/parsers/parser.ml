(* ----------------------------------------------------------------------------
  Generic Parsing Interface
---------------------------------------------------------------------------- *)
module type PARSER = sig
  type t
  exception SyntaxError of string
  exception Error
end

module ParseWithErrors (P : PARSER) : sig
  type lexer = Lexing.lexbuf -> P.t

  type 'a parser = lexer -> Lexing.lexbuf -> 'a

  val parse_with_error : 'a parser -> lexer -> Lexing.lexbuf -> 'a
  (**  *)

  val parse_from_string : 'a parser -> lexer -> string -> 'a

end = struct

  type 'a parser = (Lexing.lexbuf -> P.t) -> Lexing.lexbuf -> 'a
  type lexer = Lexing.lexbuf -> P.t

  (* Aux function: Print position information when an error occurs. *)
  let print_pos outx (lexbuf : Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    Printf.fprintf outx "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

  let parse_with_error (parser : 'a parser)
                       (lexer : lexer)
                       (lexbuf : Lexing.lexbuf) =
    try parser lexer lexbuf with
    | P.SyntaxError msg ->
      Printf.fprintf stderr "%a: %s.\n" print_pos lexbuf msg;
      exit (-1)
    | P.Error ->
      Printf.fprintf stderr "\nCould not parse string: syntax error at %a \n" print_pos lexbuf;
      exit (-1)

  let parse_from_string parser lexer (s : string) =
    let lexbuf = Lexing.from_string s in
    parse_with_error parser lexer lexbuf

  (* let parse_from_file parser lexer () *)

end
