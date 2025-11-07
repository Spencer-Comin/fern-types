open Fern_types.Depty

let {
      check_type_comp;
      infer_type_comp;
      check_type_value;
      infer_type_value;
    } =
  mk_type_system ["read"; "write"; "foo"]

let test_infer_value v ty () =
  let value = Alcotest.testable Pretty.pp_value equal_value in
  let msg =
    Fmt.str "%a should infer type %a" Pretty.pp_value v
      Pretty.pp_value ty
  in
  let ty' = infer_type_value v in
  Alcotest.(check value) msg ty ty'

let test_infer_int = test_infer_value (Int 1) IntTy
let test_infer_intty = test_infer_value IntTy (ValUniv 1)

let test_infer_val_univ =
  test_infer_value (ValUniv 1) (ValUniv 2)

let test_check_value v ty () =
  let value =
    Alcotest.testable Pretty.pp_value check_type_value
  in
  let msg =
    Fmt.str "%a should type check against %a" Pretty.pp_value v
      Pretty.pp_value ty
  in
  Alcotest.(check value) msg v ty

let test_check_val_univ =
  test_check_value (ValUniv 1) (ValUniv 2)

let test_check_u =
  test_check_value (U ([], F IntTy)) (ValUniv 1)

let test_check_sigma =
  test_check_value (Sigma ("x", IntTy, IntTy)) (ValUniv 1)

let test_check_eq =
  test_check_value (Eq (IntTy, Int 1, Int 1)) (ValUniv 1)

let test_check_thunk =
  test_check_value (Thunk (Return (Int 1))) (U ([], F IntTy))

let test_check_pair =
  test_check_value
    (Pair (Int 1, Int 2))
    (Sigma ("x", IntTy, IntTy))

let test_check_int = test_check_value (Int 1) IntTy
let test_check_intty = test_check_value IntTy (ValUniv 1)

let test_check_refl =
  test_check_value Refl (Eq (IntTy, Int 1, Int 1))

let test_check_symbol =
  test_check_value (Symbol "a_symbol")
    (SymbolSet (SymbolSet.singleton "a_symbol"))

let test_check_symbolset =
  test_check_value (SymbolSet SymbolSet.empty) (ValUniv 1)

let effects =
  let eq xs ys =
    List.length xs = List.length ys
    && List.for_all (fun x -> List.mem x ys) xs
  in
  Alcotest.testable Fmt.(list string) eq

let test_infer_comp c (ty, fx) () =
  let comp = Alcotest.testable Pretty.pp_comp equal_comp in
  let ty', fx' = infer_type_comp c in
  let msg =
    Fmt.str "%a should infer type %a with effect %a"
      Pretty.pp_comp c Pretty.pp_comp ty
      Fmt.(list string |> braces)
      fx
  in
  Alcotest.(pair comp effects |> check) msg (ty, fx) (ty', fx')

let test_comp_univ =
  test_infer_comp (CompUniv 1) (CompUniv 2, [])

let test_handler =
  let handler = Return (Int 5) in
  let expr = Handle ("foo", handler, Do "foo") in
  test_infer_comp expr (F IntTy, [])

let test_f = test_infer_comp (F IntTy) (CompUniv 1, [])

let test_f_univ =
  test_infer_comp (F (ValUniv 3)) (CompUniv 4, [])

let test_pi =
  test_infer_comp
    (Pi
       ( ["val", IntTy; "type", ValUniv 1; "univ", ValUniv 2],
         F IntTy ))
    (CompUniv 3, [])

let test_force =
  test_infer_comp (Force (Thunk (Return (Int 1)))) (F IntTy, [])

let id ty = Lam (["x", ty], Return (Var "x"))

let test_lam =
  test_infer_comp (id IntTy) (Pi (["x", IntTy], F IntTy), [])

let test_app =
  test_infer_comp (App (id IntTy, [Int 1])) (F IntTy, [])

let test_let =
  test_infer_comp
    (Let ("x", IntTy, Return (Int 1), Return (Var "x")))
    (F IntTy, [])

let test_return = test_infer_comp (Return (Int 1)) (F IntTy, [])
let test_add = test_infer_comp (Add (Int 1, Int 2)) (F IntTy, [])

let tests =
  let open Alcotest in
  let f tests =
    List.map (fun (n, t) -> test_case n `Quick t) tests
  in
  [
    ( "infer value",
      f
        [
          "Int", test_infer_int;
          "IntTy", test_infer_intty;
          "ValUniv 1", test_infer_val_univ;
        ] );
    ( "check value",
      f
        [
          "ValUniv 1", test_check_val_univ;
          "U F", test_check_u;
          "Sigma", test_check_sigma;
          "Eq", test_check_eq;
          "Thunk", test_check_thunk;
          "Pair", test_check_pair;
          "Int", test_check_int;
          "IntTy", test_check_intty;
          "Refl", test_check_refl;
          "Symbol", test_check_symbol;
          "SymbolSet", test_check_symbolset;
        ] );
    ( "infer comp",
      f
        [
          "CompUniv 1", test_comp_univ;
          "Handle", test_handler;
          "F IntTy", test_f;
          "F ValUniv", test_f_univ;
          "Pi", test_pi;
          "Force", test_force;
          "Lam", test_lam;
          "App", test_app;
          "Let", test_let;
          "Return", test_return;
          "Add", test_add;
        ] );
  ]
