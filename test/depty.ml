open Alcotest

let () =
  run "Depty"
    [
      "reduce", Depty_tests.Reduce.tests;
      "typecheck", Depty_tests.Type.tests;
    ]
