open Fern_types.Depty
open Syntax

let value ctx =
  Alcotest.testable
    (Fmt.using (Type.to_syntax_value ctx) Pretty.pp_value)
    (Type.equal_value ctx)

let test_infer_value ?(ctx = Type.mk_context ()) v ty msg () =
  let ty' = Type.infer_value ctx v in
  Alcotest.(check (value ctx))
    msg
    (Type.from_syntax_value ctx ty)
    ty'

let test_infer_int =
  test_infer_value (Int 1) IntTy
    "int value should have type int"

let test_infer_intty =
  test_infer_value IntTy (ValUniv 1)
    "int ty should have type  val univ 1"

let test_val_univ =
  test_infer_value (ValUniv 1) (ValUniv 2)
    "val univ 1 should have type val univ 2"

let comp ctx =
  Alcotest.testable
    (Fmt.using (Type.to_syntax_comp ctx) Pretty.pp_comp)
    (Type.equal_comp ctx)

let test_infer_comp ?(ctx = Type.mk_context ()) c ty msg () =
  let ty' = Type.infer_comp ctx c in
  Alcotest.(check (comp ctx))
    msg
    (Type.from_syntax_comp ctx ty)
    ty'

let test_comp_univ =
  test_infer_comp (CompUniv 1) (CompUniv 2)
    "comp univ 1 should have type comp univ 2"

let tests =
  let open Alcotest in
  [
    test_case "Int" `Quick test_infer_int;
    test_case "IntTy" `Quick test_infer_intty;
    test_case "ValUniv 1" `Quick test_val_univ;
    test_case "CompUniv 1" `Quick test_comp_univ;
  ]
