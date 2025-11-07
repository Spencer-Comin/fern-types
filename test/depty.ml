open Alcotest

let () =
  run "Depty" (Depty_tests.Reduce.tests @ Depty_tests.Type.tests)
