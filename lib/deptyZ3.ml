type context = {
  z3_ctx: Z3.context;
  int_sort: Z3.Sort.sort;
  goal: Z3.Goal.goal;
  mutable model: Z3.Model.model option;
  fx_sort: Z3.Sort.sort;
  fx_names: string list;
  fx_count: int;
}

let mk_context fx_names =
  let z3_ctx = Z3.mk_context [] in
  let int_sort = Z3.Arithmetic.Integer.mk_sort z3_ctx in
  let fx_count = List.length fx_names in
  let fx_sort = Z3.BitVector.mk_sort z3_ctx fx_count in
  {
    z3_ctx;
    int_sort;
    goal = Z3.Goal.mk_goal z3_ctx true false false;
    model = None;
    fx_sort;
    fx_names;
    fx_count;
  }

type univ = Z3.Expr.expr

let mk_var_univ {z3_ctx; int_sort; _} =
  Z3.Expr.mk_fresh_const z3_ctx "u" int_sort

let mk_const_univ {z3_ctx; _} i =
  Z3.Arithmetic.Integer.mk_numeral_i z3_ctx i

let mk_max_univ {z3_ctx; _} x y =
  let cond = Z3.Arithmetic.mk_gt z3_ctx x y in
  Z3.Boolean.mk_ite z3_ctx cond x y

exception LateConstraint

let set_eq_univ {z3_ctx; goal; model; _} x y =
  if Option.is_some model then
    raise LateConstraint;
  let eq = Z3.Boolean.mk_eq z3_ctx x y in
  Z3.Goal.add goal [eq]

let set_inc_univ {z3_ctx; goal; model; _} x y =
  if Option.is_some model then
    raise LateConstraint;
  let inc =
    Z3.Arithmetic.mk_add z3_ctx
      [y; Z3.Arithmetic.Integer.mk_numeral_i z3_ctx 1]
  in
  let eq = Z3.Boolean.mk_eq z3_ctx x inc in
  Z3.Goal.add goal [eq]

exception Unsatisfiable
exception Insufficient
exception UnknownExpr

let univ_to_int ctx x =
  let {z3_ctx; goal; model; _} = ctx in
  let model =
    if Option.is_none model then begin
      let open Z3.Solver in
      let solver = mk_simple_solver z3_ctx in
      add solver (Z3.Goal.get_formulas goal);
      match check solver [] with
      | UNKNOWN -> raise Insufficient
      | UNSATISFIABLE -> raise Unsatisfiable
      | SATISFIABLE ->
        let model = get_model solver |> Option.get in
        ctx.model <- Some model;
        model
    end
    else
      Option.get model
  in
  match Z3.Model.eval model x true with
  | None -> raise UnknownExpr
  | Some e ->
    (* this is hacky *)
    Z3.Expr.to_string e |> int_of_string

type fx = Z3.Expr.expr

let mk_var_fx {z3_ctx; fx_sort; _} =
  Z3.Expr.mk_fresh_const z3_ctx "fx" fx_sort

let mk_pure_fx {z3_ctx; fx_count; _} =
  Z3.BitVector.mk_numeral z3_ctx "0" fx_count

let mk_union_fx {z3_ctx; _} a b = Z3.BitVector.mk_or z3_ctx a b

let mk_singleton_fx {z3_ctx; fx_names; fx_count; _} s =
  (* might be better to create a bit string and convert that with Zarith *)
  let bv =
    List.find_index (String.equal s) fx_names
    |> Option.get |> Z.shift_left Z.one
  in
  Z3.BitVector.mk_numeral z3_ctx (Z.to_string bv) fx_count

let mk_const_fx {z3_ctx; fx_names; fx_count; _} fx =
  let bv =
    List.map
      (fun s ->
        List.find_index (String.equal s) fx_names
        |> Option.get |> Z.shift_left Z.one)
      fx
    |> List.fold_left Z.logor Z.zero
  in
  Z3.BitVector.mk_numeral z3_ctx (Z.to_string bv) fx_count

let set_eq_fx = set_eq_univ

let set_lte_fx {z3_ctx; goal; model; _} x y =
  if Option.is_some model then
    raise LateConstraint;
  let union = Z3.BitVector.mk_or z3_ctx x y in
  let eq = Z3.Boolean.mk_eq z3_ctx union y in
  Z3.Goal.add goal [eq]

let fx_to_string_list ctx fx =
  let {z3_ctx; goal; model; fx_names; _} = ctx in
  let model =
    if Option.is_none model then begin
      let open Z3.Solver in
      let solver = mk_simple_solver z3_ctx in
      add solver (Z3.Goal.get_formulas goal);
      match check solver [] with
      | UNKNOWN -> raise Insufficient
      | UNSATISFIABLE -> raise Unsatisfiable
      | SATISFIABLE ->
        let model = get_model solver |> Option.get in
        ctx.model <- Some model;
        model
    end
    else
      Option.get model
  in
  let bv =
    match Z3.Model.eval model fx true with
    | None -> raise UnknownExpr
    | Some e ->
      (* this is hacky *)
      let format_convert s =
        (* remove '#' prefix and replace with '0' *)
        let len = String.length s in
        "0" ^ String.sub s 1 (len - 1)
      in
      Z3.Expr.to_string e |> format_convert |> Z.of_string
  in
  List.mapi
    (fun i e ->
      if Z.testbit bv i then
        [e]
      else
        [])
    fx_names
  |> List.concat

let mk_remove_fx ctx fx e =
  let mask =
    Z3.BitVector.mk_not ctx.z3_ctx (mk_singleton_fx ctx e)
  in
  Z3.BitVector.mk_and ctx.z3_ctx fx mask
