(lang dune 3.15)

(name oyula)

(generate_opam_files true)

(source
 (github glyh/oyula))

(authors "Yihang Liu")

(maintainers "Yihang Liu")

(license GPL-3.0-or-later)

(documentation https://github.com/glyh/oyula)

(package
 (name oyula)
 (synopsis "Yula Compiler implemented in OCaml.")
 (description "Yula Compiler implemented in OCaml.")
 (depends
   ocaml
   dune
   (angstrom (>= 0.16.0))
   (core (>= 0.16.2))
   (ppx_inline_test (>= 0.14.1))
   (ppx_deriving (>= 6.0.2))
   (ppx_sexp_conv (>= 0.16.0)))
 (tags
  (topics compiler)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
