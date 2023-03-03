(lang dune 3.6)

(name konijn)

(version 0.1.0)

(using menhir 2.1)

(generate_opam_files true)

(source
 (github deividrvale/konijn))

(authors "Deivid Vale")

(maintainers "Deivid Vale")

(license GNU GPLv3)

(documentation https://github.com/deividrvale/konijn)

(package
 (name konijn)
 (synopsis "Konijn is a termination/complexity analysis tool for higher-order rewriting.")
 (description "")
 (depends
  (ocaml
   (>= 4.14.1))
  (dune
   (>= 3.6.2))
  (menhir
   (>= 20220210)))
 (tags
  (topics
   "termination analysis"
   "higher-order rewriting"
   "complexity analysis"
   "automatic proving")))
