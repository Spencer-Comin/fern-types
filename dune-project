(lang dune 3.14)

(name fern_types)

(generate_opam_files true)

(source
 (github Spencer-Comin/fern-types))

(authors "Spencer Comin")

(maintainers "Spencer Comin")

(license unlicensed)

(documentation undocumented)

(package
 (name fern_types)
 (synopsis "Compiling dependent CBPV")
 (description
  "An exploration of compiling a dependently typed call-by-push-value calculus")
 (depends
  ocaml
  dune
  fmt
  zarith
  z3
  (alcotest :with-test))
 (tags
  (compilers "type theory" "dependent types" call-by-push-value)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
