open Fern_types.Depty

let value = Alcotest.testable Pretty.pp_value equal_value

let {
      check_type_comp;
      infer_type_comp;
      check_type_value;
      infer_type_value;
    } =
  mk_type_system ["read"; "write"]

let test_infer_value v ty msg () =
  let ty' = infer_type_value v in
  Alcotest.(check value) msg ty ty'

let test_infer_int =
  test_infer_value (Int 1) IntTy
    "int value should have type int"

let test_infer_intty =
  test_infer_value IntTy (ValUniv 1)
    "int ty should have type  val univ 1"

let test_val_univ =
  test_infer_value (ValUniv 1) (ValUniv 2)
    "val univ 1 should have type val univ 2"

let comp =
  Alcotest.testable
    Pretty.pp_comp
    equal_comp

let effects =
  let eq xs ys =
    List.length xs = List.length ys
    && List.for_all (fun x -> List.mem x ys) xs
  in
  Alcotest.testable Fmt.(list string) eq

let test_infer_comp c (ty, fx) msg () =
  let ty', fx' = infer_type_comp c in
  Alcotest.(pair comp effects |> check)
      msg
      (ty, fx)
      (ty', fx')

let test_comp_univ =
  test_infer_comp (CompUniv 1) (CompUniv 2, [])
    "comp univ 1 should have type comp univ 2"

let tests =
  let open Alcotest in
  [
    test_case "Int" `Quick test_infer_int;
    test_case "IntTy" `Quick test_infer_intty;
    test_case "ValUniv 1" `Quick test_val_univ;
    test_case "CompUniv 1" `Quick test_comp_univ;
  ]
