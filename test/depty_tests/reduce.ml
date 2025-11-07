open Fern_types.Depty

let stlc_id ty = Lam (["x", ty], Return (Var "x"))

let pi_id =
  Lam (["X", ValUniv 1], Lam (["x", Var "X"], Return (Var "x")))

let two = Int 2
let apply f xs = reduce (App (f, xs))
let comp = Alcotest.testable Pretty.pp_comp equal_comp

let test_stlc_id () =
  Alcotest.(check comp)
    "same STLC id of two" (Return two)
    (apply (stlc_id IntTy) [two])

let test_pi_id () =
  Alcotest.(check comp)
    "same dependent Pi id of two" (Return two)
    (apply (apply pi_id [IntTy]) [two])

let test_force () =
  let expr = Force (Thunk (Return (Int 5))) |> reduce in
  Alcotest.(check comp) "force thunk" expr (Return (Int 5))

let test_let () =
  let expr =
    Let ("x", IntTy, Return (Int 42), Return (Var "x"))
    |> reduce
  in
  Alcotest.(check comp) "let" expr (Return (Int 42))

let test_dlet () =
  let expr =
    DLet ("x", IntTy, Return (Int 42), Return (Var "x"))
    |> reduce
  in
  Alcotest.(check comp) "let" expr (Return (Int 42))

let test_let_add () =
  let expr =
    Let
      ( "x",
        IntTy,
        Return (Int 5),
        Let ("y", IntTy, Return (Int 7), Add (Var "x", Var "y"))
      )
    |> reduce
  in
  Alcotest.(check comp) "let add" expr (Return (Int 12))

let test_recsigma () =
  let v = Pair (Int 5, Int 7) in
  let v_ty = Sigma ("_", IntTy, IntTy) in
  let mot = Lam (["_", v_ty], F IntTy) in
  let expr =
    RecSigma
      ( v,
        mot,
        Lam (["x", IntTy; "y", IntTy], Add (Var "x", Var "y"))
      )
    |> reduce
  in
  Alcotest.(check comp) "add pair" expr (Return (Int 12))

let test_receq () =
  let expr = RecEq (Refl, F IntTy, Return (Int 5)) |> reduce in
  Alcotest.(check comp) "simple refl" expr (Return (Int 5))

let test_alpha_eq () =
  let a = Lam (["a", IntTy], Return (Var "a")) in
  let b = Lam (["b", IntTy], Return (Var "b")) in
  Alcotest.(check comp) "alpha eq id" a b

let test_simple_handler () =
  let handler = Return (Int 5) in
  let expr = Handle ("foo", handler, Do "foo") |> reduce in
  Alcotest.(check comp) "simple handler" expr handler

let test_apply_handler () =
  let expr =
    Handle ("foo", stlc_id IntTy, App (Do "foo", [Int 5]))
    |> reduce
  in
  Alcotest.(check comp) "apply handler" expr (Return (Int 5))

let tests =
  let open Alcotest in
  [
    test_case "STLC id" `Quick test_stlc_id;
    test_case "Pi id" `Quick test_pi_id;
    test_case "sum pair" `Quick test_recsigma;
    test_case "receq refl" `Quick test_receq;
    test_case "thunked return" `Quick test_force;
    test_case "let" `Quick test_let;
    test_case "dlet" `Quick test_dlet;
    test_case "let add" `Quick test_let_add;
    test_case "id alpha eq" `Quick test_alpha_eq;
    test_case "simple handler" `Quick test_simple_handler;
    test_case "apply handler" `Quick test_apply_handler;
  ]
