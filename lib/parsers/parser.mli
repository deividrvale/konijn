(** This module provides abstract interfacing for parsing input files.

    {b Note:}
    Each new file format added to {b onijn} is a concrete implementation of
    this abstract interfacing.
*)

module type PARSER = sig
    type t
    (** Abstract type for for tokens. *)

    exception SyntaxError of string
    (** Exception thrown whenever the lexer encounters a syntax error in the input file. *)

    exception Error
    (** Exception thrown whenever the parser reaches an error state. *)
end
(** This module type provides an abstract interface for parsing. *)

module ParseWithErrors : functor (P : PARSER) -> sig

    type lexer = Lexing.lexbuf -> P.t

    type 'a parser = lexer -> Lexing.lexbuf -> 'a

    val parse_with_error : 'a parser -> lexer -> Lexing.lexbuf -> 'a

    val parse_from_string : 'a parser -> lexer -> string -> 'a
end
(** This functor provides a default implementation for a concrete parser
    that support 'exit on error' parsing.
*)
