(* ∂CBPV *)
(* TODO:
   - lowering to IR
   - effects & coeffects (https://dl.acm.org/doi/10.1145/3689750)
   - effect handlers
   - recursion
   - control effects
   - make Add a function
   - symbol set unification
   - set ops on SymbolSet *)

module SymbolSet = Set.Make (String)
module SymbolMap = Map.Make (String)

type eff = string
type fx = eff list

module Syntax = struct
  type value_ty = value
  and comp_ty = comp

  and value =
    | ValUniv of int
    | U of fx * comp_ty
    | Sigma of string * value_ty * value_ty
    | Eq of value_ty * value * value
    | Var of string
    | Thunk of comp
    | Pair of value * value
    | Int of int
    | IntTy
    | Refl
    | Symbol of string
    | SymbolSet of SymbolSet.t

  and comp =
    | CompUniv of int
    | F of value_ty
    | Pi of (string * value_ty) list * comp_ty
    | Force of value
    | Lam of (string * value_ty) list * comp
    | App of comp * value list
    | Let of string * value_ty * comp * comp
    | DLet of string * value_ty * comp * comp
    | Return of value
    | RecSigma of value * comp * comp
    | RecSym of value * comp * comp SymbolMap.t
    | RecEq of value * comp_ty * comp
    | Add of value * value
    | Do of eff
    | Handle of eff * comp * comp

  module Pretty = struct
    let rec subscript i =
      assert (i >= 0);
      let nums =
        [|"₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"|]
      in
      if i < 10 then
        nums.(i)
      else
        subscript (i / 10) ^ nums.(i mod 10)

    let pp_annotated (pp_a : 'a Fmt.t) (pp_b : 'b Fmt.t) :
        ('a * 'b) Fmt.t =
     fun ppf (a, b) ->
      let open Fmt in
      pf ppf "%a:%a" (pp_a ++ sp) a (sp ++ pp_b) b

    let pp_dot (pp_a : 'a Fmt.t) (pp_b : 'b Fmt.t) :
        ('a * 'b) Fmt.t =
     fun ppf (a, b) ->
      let open Fmt in
      pf ppf "%a.%a" pp_a a (sp ++ box ~indent:1 pp_b) b

    let pp_typed (pp_a : 'a Fmt.t) (pp_b : 'b Fmt.t)
        (pp_c : 'c Fmt.t) : ('a * 'b * 'c) Fmt.t =
     fun ppf (a, b, c) ->
      (*a: b. c*)
      let open Fmt in
      pf ppf "%a"
        (pp_dot (pp_annotated pp_a pp_b) pp_c)
        ((a, b), c)

    let triple (pp_a : 'a Fmt.t) (pp_b : 'b Fmt.t)
        (pp_c : 'c Fmt.t) : ('a * 'b * 'c) Fmt.t =
     fun ppf (a, b, c) ->
      let open Fmt in
      pf ppf "%a%a%a" pp_a a pp_b b pp_c c

    let quad (pp_a : 'a Fmt.t) (pp_b : 'b Fmt.t)
        (pp_c : 'c Fmt.t) (pp_d : 'd Fmt.t) :
        ('a * 'b * 'c * 'd) Fmt.t =
     fun ppf (a, b, c, d) ->
      let open Fmt in
      pf ppf "%a%a%a%a" pp_a a pp_b b pp_c c pp_d d

    let of_str s : unit Fmt.t =
     fun ppf () ->
      let open Fmt in
      pf ppf "%a" string s

    let rec pp_value : value Fmt.t =
     fun ppf ->
      let open Fmt in
      function
      | Var x -> pf ppf "%a" string x
      | Int i -> pf ppf "%a" int i
      | Refl -> pf ppf "refl"
      | IntTy -> pf ppf "Int"
      | ValUniv i -> pf ppf "█ᵛ%a" string (subscript i)
      | U (es, c) ->
        pf ppf "U %a%a"
          (list ~sep:comma string |> brackets)
          es (sp ++ pp_comp) c
      | Sigma (x, s, t) ->
        pf ppf "∑ %a"
          (pp_typed string pp_value pp_value)
          (x, s, t)
      | Eq (a, v, w) ->
        pf ppf "eq %a" (list ~sep:sp pp_value) [a; v; w]
      | Thunk c -> pf ppf "thunk %a" pp_comp c
      | Pair (u, v) ->
        pf ppf "%a" (list ~sep:comma pp_value |> parens) [u; v]
      | Symbol s -> pf ppf "%a" string s
      | SymbolSet s ->
        pf ppf "%a"
          (list ~sep:comma string |> braces)
          (SymbolSet.to_list s)

    and pp_comp : comp Fmt.t =
     fun ppf ->
      let open Fmt in
      function
      | CompUniv i -> pf ppf "█ᶜ%a" string (subscript i)
      | F t -> pf ppf "F %a" pp_value t
      | Pi ([(x, s)], t) ->
        pf ppf "∏ %a"
          (pp_typed string pp_value pp_comp)
          (x, s, t)
      | Pi (xs, t) ->
        pf ppf "∏ %a"
          (pp_dot
             (list (pp_annotated string pp_value |> parens))
             pp_comp)
          (xs, t)
      | Force v -> pf ppf "force %a" pp_value v
      | Lam ([(x, s)], t) ->
        pf ppf "λ %a"
          (pp_typed string pp_value pp_comp)
          (x, s, t)
      | Lam (xs, t) ->
        pf ppf "λ %a"
          (pp_dot
             (list (pp_annotated string pp_value |> parens))
             pp_comp)
          (xs, t)
      | App (f, t) ->
        pf ppf "%a%a" (pp_comp ++ sp) f
          (list ~sep:comma pp_value |> parens)
          t
      | Let (x, a, t, u) ->
        pf ppf "let %a:%a=%ain%a" (string ++ sp) x
          (sp ++ pp_value ++ sp)
          a
          (sp ++ hvbox ~indent:1 pp_comp ++ sp)
          t (sp ++ pp_comp) u
      | DLet (x, a, t, u) ->
        pf ppf "let dep %a:%a=%ain%a" (string ++ sp) x
          (sp ++ pp_value ++ sp)
          a
          (box ~indent:1 pp_comp ++ sp)
          t (sp ++ pp_comp) u
      | Return v -> pf ppf "return %a" pp_value v
      | RecEq (v, x, t) | RecSigma (v, x, t) ->
        pf ppf "rec%a"
          (triple (pp_value ++ comma) (pp_comp ++ comma) pp_comp
          |> parens)
          (v, x, t)
      | RecSym (v, m, cs) ->
        pf ppf "rec%a"
          (triple (pp_value ++ comma) (pp_comp ++ comma)
             (list ~sep:semi
                (pair
                   ~sep:(sp ++ of_str "->" ++ sp)
                   string pp_comp)
             |> brackets)
          |> parens)
          (v, m, SymbolMap.to_list cs)
      | Add (u, v) ->
        pf ppf "%a+%a" (pp_value ++ sp) u (sp ++ pp_value) v
      | Do e -> pf ppf "do %a" string e
      | Handle (e, a, b) ->
        pf ppf "with %a=%ahandle%a" (string ++ sp) e
          (sp ++ hvbox ~indent:1 pp_comp ++ sp)
          a (sp ++ pp_comp) b
  end
end

module SMap = Map.Make (String)

module Core = struct
  type weak_comp_ty = weak_comp
  and weak_value_ty = weak_value

  and env = {
    values: weak_value SMap.t;
    handlers: (env * Syntax.comp) SMap.t;
  }

  and weak_value =
    | NVal of neutral_value
    | ValUniv of int
    | U of env * fx * Syntax.comp_ty
    | Sigma of string * weak_value_ty * (env * Syntax.value_ty)
    | Eq of weak_value_ty * weak_value * weak_value
    | Thunk of env * Syntax.comp
    | Pair of weak_value * weak_value
    | Int of int
    | IntTy
    | Refl
    | Symbol of string
    | SymbolSet of SymbolSet.t

  and neutral_value = Var of string

  and weak_comp =
    | NComp of neutral_comp
    | CompUniv of int
    | F of weak_value_ty
    | Pi of
        (string * weak_value_ty) list * (env * Syntax.comp_ty)
    | Lam of (string * weak_value_ty) list * (env * Syntax.comp)
    | Return of weak_value

  and neutral_comp =
    | App of neutral_comp * weak_value list
    | Force of neutral_value
    | RecSigma of neutral_value * weak_comp * weak_comp
    | RecEq of neutral_value * weak_comp * weak_comp
    | RecSym of
        neutral_value * weak_comp * weak_comp SymbolMap.t
    | Add of neutral_value * weak_value
    | Do of eff

  exception Stuck

  let rec apply f vs =
    match f with
    | Lam (xs, (env, f)) ->
      let values =
        List.fold_left2
          begin
            fun env (x, _) v -> SMap.add x v env
          end
          env.values xs vs
      in
      reduce {env with values} f
    | NComp n -> NComp (App (n, vs))
    | _ -> raise Stuck

  and resolve (env : env) = function
    | Syntax.Var x ->
      SMap.find_opt x env.values
      |> Option.value ~default:(NVal (Var x))
    | Syntax.ValUniv i -> ValUniv i
    | Syntax.U (e, t) -> U (env, e, t)
    | Syntax.Sigma (x, a, b) ->
      Sigma (x, resolve env a, (env, b))
    | Syntax.Eq (a, v, w) ->
      Eq (resolve env a, resolve env v, resolve env w)
    | Syntax.Thunk t -> Thunk (env, t)
    | Syntax.Pair (u, v) -> Pair (resolve env u, resolve env v)
    | Syntax.Int i -> Int i
    | Syntax.IntTy -> IntTy
    | Syntax.Refl -> Refl
    | Syntax.Symbol s -> Symbol s
    | Syntax.SymbolSet ss -> SymbolSet ss

  and reduce (env : env) = function
    | Syntax.App (f, vs) ->
      apply (reduce env f) (List.map (resolve env) vs)
    | Syntax.Let (x, _, t, u) | DLet (x, _, t, u) -> begin
      match reduce env t with
      | Return v ->
        reduce {env with values = SMap.add x v env.values} u
      | _ -> raise Stuck
    end
    | Syntax.Force v -> begin
      match resolve env v with
      | Thunk (env', t) -> reduce env' t
      | NVal n -> NComp (Force n)
      | _ -> raise Stuck
    end
    | Syntax.RecSigma (v, x, t) -> begin
      match resolve env v with
      | Pair (v, w) -> apply (reduce env t) [v; w]
      | NVal n ->
        NComp (RecSigma (n, reduce env x, reduce env t))
      | _ -> raise Stuck
    end
    | Syntax.RecEq (v, x, t) -> begin
      match resolve env v with
      | Refl -> reduce env t
      | NVal n -> NComp (RecEq (n, reduce env x, reduce env t))
      | _ -> raise Stuck
    end
    | Syntax.RecSym (v, m, cs) -> begin
      match resolve env v with
      | Symbol s -> reduce env (SymbolMap.find s cs)
      | NVal n ->
        NComp
          (RecSym
             (n, reduce env m, SymbolMap.map (reduce env) cs))
      | _ -> raise Stuck
    end
    | Syntax.Add (u, v) -> begin
      match resolve env u, resolve env v with
      | Int i, Int j -> Return (Int (i + j))
      | NVal n, v | v, NVal n -> NComp (Add (n, v))
      | _ -> raise Stuck
    end
    | Syntax.CompUniv i -> CompUniv i
    | Syntax.F v -> F (resolve env v)
    | Syntax.Pi (xs, t) ->
      Pi (List.map (fun (x, a) -> x, resolve env a) xs, (env, t))
    | Syntax.Lam (xs, t) ->
      Lam
        (List.map (fun (x, a) -> x, resolve env a) xs, (env, t))
    | Syntax.Return v -> Return (resolve env v)
    | Syntax.Do e -> begin
      match SMap.find_opt e env.handlers with
      | Some (env', c) -> reduce env' c
      | None -> NComp (Do e)
    end
    | Syntax.Handle (e, a, b) ->
      reduce
        {env with handlers = SMap.add e (env, a) env.handlers}
        b

  and quote_value : weak_value -> Syntax.value = function
    | ValUniv i -> Syntax.ValUniv i
    | U (_, e, c) -> Syntax.U (e, c)
    | Sigma (x, a, (_, b)) -> Sigma (x, quote_value a, b)
    | Eq (x, u, v) ->
      Eq (quote_value x, quote_value u, quote_value v)
    | Thunk (_, t) -> Thunk t
    | Pair (u, v) -> Pair (quote_value u, quote_value v)
    | Int i -> Int i
    | IntTy -> IntTy
    | Refl -> Refl
    | NVal n -> quote_nvalue n
    | Symbol s -> Symbol s
    | SymbolSet ss -> SymbolSet ss

  and quote_nvalue (Var x) = Syntax.Var x

  and quote_comp = function
    | CompUniv i -> Syntax.CompUniv i
    | F u -> Syntax.F (quote_value u)
    | Pi (xs, (_, f)) ->
      Syntax.Pi (List.map (fun (x, t) -> x, quote_value t) xs, f)
    | Lam (xs, (_, f)) ->
      Syntax.Lam
        (List.map (fun (x, t) -> x, quote_value t) xs, f)
    | Return v -> Syntax.Return (quote_value v)
    | NComp n -> quote_ncomp n

  and quote_ncomp = function
    | App (f, vs) ->
      Syntax.App (quote_ncomp f, List.map quote_value vs)
    | Force v -> Syntax.Force (quote_nvalue v)
    | RecSigma (n, t, c) ->
      Syntax.RecSigma
        (quote_nvalue n, quote_comp t, quote_comp c)
    | RecEq (n, t, c) ->
      Syntax.RecEq (quote_nvalue n, quote_comp t, quote_comp c)
    | RecSym (n, m, cs) ->
      Syntax.RecSym
        ( quote_nvalue n,
          quote_comp m,
          SymbolMap.map quote_comp cs )
    | Add (u, v) -> Syntax.Add (quote_nvalue u, quote_value v)
    | Do e -> Syntax.Do e

  let rec equal_value u_stack v_stack u v =
    match u, v with
    | NVal m, NVal n -> equal_nvalue u_stack v_stack m n
    | ValUniv i, ValUniv j -> i = j
    | U (env, e, a), U (env', f, b) ->
      List.for_all (fun e -> List.mem e f) e
      && equal_comp u_stack v_stack (reduce env a)
           (reduce env' b)
    | Sigma (x, t, (env, u)), Sigma (y, s, (env', v)) ->
      equal_value u_stack v_stack t s
      && equal_value (x :: u_stack) (y :: v_stack)
           (resolve env u) (resolve env' v)
    | Eq (a, u, v), Eq (b, w, x) ->
      equal_value u_stack v_stack a b
      && (equal_value u_stack v_stack u w
          && equal_value u_stack v_stack v x
         || equal_value u_stack v_stack u x
            && equal_value u_stack v_stack v w)
    | Thunk (env, a), Thunk (env', b) ->
      equal_comp u_stack v_stack (reduce env a) (reduce env' b)
    | Pair (u, v), Pair (w, x) ->
      equal_value u_stack v_stack u w
      && equal_value u_stack v_stack v x
    | Int i, Int j -> i = j
    | IntTy, IntTy -> true
    | Refl, Refl -> true
    | Symbol s, Symbol t -> s = t
    | SymbolSet ss, SymbolSet ts -> SymbolSet.equal ss ts
    | _ -> false

  and equal_nvalue u_stack v_stack (Var x) (Var y) =
    match
      ( List.find_index (String.equal x) u_stack,
        List.find_index (String.equal y) v_stack )
    with
    | Some i, Some j -> i = j
    | None, None -> String.equal x y
    | _ -> false

  and equal_comp u_stack v_stack a b =
    match a, b with
    | NComp m, NComp n -> equal_ncomp u_stack v_stack m n
    | CompUniv i, CompUniv j -> i = j
    | F u, F v -> equal_value u_stack v_stack u v
    | Pi (xs, (env, a)), Pi (ys, (env', b))
    | Lam (xs, (env, a)), Lam (ys, (env', b)) -> begin
      let check (u_stack, v_stack) (x, t) (y, s) =
        if equal_value u_stack v_stack t s then
          x :: u_stack, y :: v_stack
        else
          raise Exit
      in
      try
        let u_stack, v_stack =
          List.fold_left2 check (u_stack, v_stack) xs ys
        in
        equal_comp u_stack v_stack (reduce env a)
          (reduce env' b)
      with Exit -> false
    end
    | Return u, Return v -> equal_value u_stack v_stack u v
    | _ -> false

  and equal_ncomp u_stack v_stack m n =
    match m, n with
    | App (m, us), App (n, vs) ->
      equal_ncomp u_stack v_stack m n
      && List.for_all2 (equal_value u_stack v_stack) us vs
    | Force m, Force n -> equal_nvalue u_stack v_stack m n
    | RecSigma (m, a, b), RecSigma (n, c, d)
    | RecEq (m, a, b), RecEq (n, c, d) ->
      equal_nvalue u_stack v_stack m n
      && equal_comp u_stack v_stack a c
      && equal_comp u_stack v_stack b d
    | RecSym (m, a, bs), RecSym (n, c, ds) ->
      equal_nvalue u_stack v_stack m n
      && equal_comp u_stack v_stack a c
      && SymbolMap.equal (equal_comp u_stack v_stack) bs ds
    | Add (m, u), Add (n, v) ->
      equal_nvalue u_stack v_stack m n
      && equal_value u_stack v_stack u v
    | Do _, Do _ -> (* TODO: fix me? *) false
    | _ -> false

  let equal_value = equal_value [] []
  let equal_comp = equal_comp [] []
end

(* Typing *)
module Type = struct
  type value_ty = value
  and comp_ty = comp

  and value =
    | ValUniv of DeptyZ3.univ
    | U of DeptyZ3.fx * comp_ty
    | Sigma of string * value_ty * (Core.weak_value -> value_ty)
    | Eq of value_ty * Core.weak_value * Core.weak_value
    | Var of string
    | Thunk of comp
    | Pair of value * value
    | Int of int
    | IntTy
    | Refl
    | Symbol of string
    | SymbolSet of SymbolSet.t

  and comp =
    | CompUniv of DeptyZ3.univ
    | F of value_ty
    | Pi of
        (string * value_ty) list
        * (Core.weak_value list -> comp_ty * DeptyZ3.fx)
    | Force of value
    | Lam of
        (string * value_ty) list
        * (Core.weak_value list -> comp_ty)
    | App of comp * value list
    | Let of string * value_ty * comp * comp
    | DLet of string * value_ty * comp * comp
    | Return of value
    | RecSigma of value * comp * comp
    | RecSym of value * comp * comp SymbolMap.t
    | RecEq of value * comp * comp
    | Add of value * value
    | Do of DeptyZ3.fx
    | Handle of eff * comp * comp

  type context = {
    ty_ctx: value_ty SMap.t;
    handler_ty_ctx: comp_ty SMap.t;
    env: Core.env;
    z3_ctx: DeptyZ3.context;
  }

  let add_val ctx x v =
    let env = ctx.env in
    let env = {env with values = SMap.add x v env.values} in
    {ctx with env}

  let add_ty ctx x t =
    {ctx with ty_ctx = SMap.add x t ctx.ty_ctx}

  let mk_context effect_list =
    {
      ty_ctx = SMap.empty;
      handler_ty_ctx = SMap.empty;
      env = {values = SMap.empty; handlers = SMap.empty};
      z3_ctx = DeptyZ3.mk_context effect_list;
    }

  let rec from_syntax_value ctx = function
    | Syntax.ValUniv i ->
      ValUniv (DeptyZ3.mk_const_univ ctx.z3_ctx i)
    | Syntax.U (es, c) ->
      U
        ( DeptyZ3.mk_const_fx ctx.z3_ctx es,
          from_syntax_comp ctx c )
    | Syntax.Sigma (x, a, b) ->
      let a' = from_syntax_value ctx a in
      let b' v =
        let ctx' =
          {
            ctx with
            env =
              {
                ctx.env with
                values = SMap.add x v ctx.env.values;
              };
            ty_ctx = SMap.add x a' ctx.ty_ctx;
          }
        in
        Core.resolve ctx'.env b
        |> Core.quote_value
        |> from_syntax_value ctx'
      in
      Sigma (x, a', b')
    | Syntax.Eq (a, u, v) ->
      Eq
        ( from_syntax_value ctx a,
          Core.resolve ctx.env u,
          Core.resolve ctx.env v )
    | Syntax.Var x -> Var x
    | Syntax.Thunk c -> Thunk (from_syntax_comp ctx c)
    | Syntax.Pair (u, v) ->
      Pair (from_syntax_value ctx u, from_syntax_value ctx v)
    | Syntax.Int i -> Int i
    | Syntax.IntTy -> IntTy
    | Syntax.Refl -> Refl
    | Syntax.Symbol s -> Symbol s
    | Syntax.SymbolSet ss -> SymbolSet ss

  and from_syntax_comp ctx = function
    | Syntax.CompUniv i ->
      CompUniv (DeptyZ3.mk_const_univ ctx.z3_ctx i)
    | Syntax.F v -> F (from_syntax_value ctx v)
    | Syntax.Pi (xs, t) ->
      let folder ctx (x, ty) =
        let ty' = from_syntax_value ctx ty in
        {ctx with ty_ctx = SMap.add x ty' ctx.ty_ctx}, (x, ty')
      in
      let ctx', xs' = List.fold_left_map folder ctx xs in
      let t' vs =
        let ctx'' =
          List.fold_left2 add_val ctx' (List.map fst xs) vs
        in
        ( Core.reduce ctx''.env t
          |> Core.quote_comp
          |> from_syntax_comp ctx'',
          DeptyZ3.mk_var_fx ctx.z3_ctx )
      in
      Pi (xs', t')
    | Syntax.Force v -> Force (from_syntax_value ctx v)
    | Syntax.Lam (xs, t) ->
      let folder ctx (x, ty) =
        let ty' = from_syntax_value ctx ty in
        {ctx with ty_ctx = SMap.add x ty' ctx.ty_ctx}, (x, ty')
      in
      let ctx', xs' = List.fold_left_map folder ctx xs in
      let t' vs =
        let ctx'' =
          List.fold_left2 add_val ctx' (List.map fst xs) vs
        in
        Core.reduce ctx''.env t
        |> Core.quote_comp
        |> from_syntax_comp ctx''
      in
      Lam (xs', t')
    | Syntax.App (c, vs) ->
      App
        ( from_syntax_comp ctx c,
          List.map (from_syntax_value ctx) vs )
    | Syntax.Let (x, a, t, u) ->
      let a' = from_syntax_value ctx a in
      Let
        ( x,
          a',
          from_syntax_comp ctx t,
          from_syntax_comp
            {ctx with ty_ctx = SMap.add x a' ctx.ty_ctx}
            u )
    | Syntax.DLet (x, a, t, u) ->
      let a' = from_syntax_value ctx a in
      DLet
        ( x,
          a',
          from_syntax_comp ctx t,
          from_syntax_comp
            {ctx with ty_ctx = SMap.add x a' ctx.ty_ctx}
            u )
    | Syntax.Return v -> Return (from_syntax_value ctx v)
    | Syntax.RecSigma (v, m, c) ->
      RecSigma
        ( from_syntax_value ctx v,
          from_syntax_comp ctx m,
          from_syntax_comp ctx c )
    | Syntax.RecSym (v, m, cs) ->
      RecSym
        ( from_syntax_value ctx v,
          from_syntax_comp ctx m,
          SymbolMap.map (from_syntax_comp ctx) cs )
    | Syntax.RecEq (v, m, c) ->
      RecEq
        ( from_syntax_value ctx v,
          from_syntax_comp ctx m,
          from_syntax_comp ctx c )
    | Syntax.Add (u, v) ->
      Add (from_syntax_value ctx u, from_syntax_value ctx v)
    | Syntax.Do e -> Do (DeptyZ3.mk_singleton_fx ctx.z3_ctx e)
    | Syntax.Handle (e, a, b) ->
      Handle (e, from_syntax_comp ctx a, from_syntax_comp ctx b)

  let rec to_syntax_value ctx = function
    | ValUniv i ->
      Syntax.ValUniv (DeptyZ3.univ_to_int ctx.z3_ctx i)
    | U (es, t) ->
      Syntax.U
        ( DeptyZ3.fx_to_string_list ctx.z3_ctx es,
          to_syntax_comp ctx t )
    | Sigma (x, s, t) ->
      Syntax.Sigma
        ( x,
          to_syntax_value ctx s,
          to_syntax_value ctx (Core.NVal (Core.Var x) |> t) )
    | Eq (t, u, v) ->
      Syntax.Eq
        ( to_syntax_value ctx t,
          Core.quote_value u,
          Core.quote_value v )
    | Var x -> Syntax.Var x
    | Thunk c -> Syntax.Thunk (to_syntax_comp ctx c)
    | Pair (u, v) ->
      Syntax.Pair (to_syntax_value ctx u, to_syntax_value ctx v)
    | Int i -> Syntax.Int i
    | IntTy -> Syntax.IntTy
    | Refl -> Syntax.Refl
    | Symbol s -> Syntax.Symbol s
    | SymbolSet ss -> Syntax.SymbolSet ss

  and to_syntax_comp ctx = function
    | CompUniv i ->
      Syntax.CompUniv (DeptyZ3.univ_to_int ctx.z3_ctx i)
    | F t -> Syntax.F (to_syntax_value ctx t)
    | Pi (xs, f) ->
      let folder (xs, vars) (x, t) =
        ( (x, to_syntax_value ctx t) :: xs,
          Core.NVal (Core.Var x) :: vars )
      in
      let xs, vars = List.fold_left folder ([], []) xs in
      Syntax.Pi (xs, f vars |> fst |> to_syntax_comp ctx)
    | Lam (xs, f) ->
      let folder (xs, vars) (x, t) =
        ( (x, to_syntax_value ctx t) :: xs,
          Core.NVal (Core.Var x) :: vars )
      in
      let xs, vars = List.fold_left folder ([], []) xs in
      Syntax.Lam (xs, f vars |> to_syntax_comp ctx)
    | App (f, vs) ->
      Syntax.App
        (to_syntax_comp ctx f, List.map (to_syntax_value ctx) vs)
    | Let (x, t, a, b) ->
      Syntax.Let
        ( x,
          to_syntax_value ctx t,
          to_syntax_comp ctx a,
          to_syntax_comp ctx b )
    | DLet (x, t, a, b) ->
      Syntax.DLet
        ( x,
          to_syntax_value ctx t,
          to_syntax_comp ctx a,
          to_syntax_comp ctx b )
    | Return v -> Syntax.Return (to_syntax_value ctx v)
    | RecSigma (v, m, t) ->
      Syntax.RecSigma
        ( to_syntax_value ctx v,
          to_syntax_comp ctx m,
          to_syntax_comp ctx t )
    | RecEq (v, m, t) ->
      Syntax.RecEq
        ( to_syntax_value ctx v,
          to_syntax_comp ctx m,
          to_syntax_comp ctx t )
    | RecSym (v, m, ts) ->
      Syntax.RecSym
        ( to_syntax_value ctx v,
          to_syntax_comp ctx m,
          SymbolMap.map (to_syntax_comp ctx) ts )
    | Add (u, v) ->
      Syntax.Add (to_syntax_value ctx u, to_syntax_value ctx v)
    | Force v -> Syntax.Force (to_syntax_value ctx v)
    | Do e ->
      Syntax.Do
        (DeptyZ3.fx_to_string_list ctx.z3_ctx e |> List.hd)
    | Handle (e, a, b) ->
      Syntax.Handle
        (e, to_syntax_comp ctx a, to_syntax_comp ctx b)

  (* Only considering alpha-equivalency *)
  let rec equal_value u_ctx v_ctx u v =
    match u, v with
    | ValUniv u, ValUniv w ->
      DeptyZ3.set_eq_univ u_ctx.z3_ctx u w;
      true
    | U (es, a), U (fs, b) ->
      equal_comp u_ctx v_ctx a b
      &&
      (DeptyZ3.set_eq_fx u_ctx.z3_ctx es fs;
       true)
    | Sigma (x, u, f), Sigma (_, v, g) ->
      equal_value u_ctx v_ctx u v
      &&
      let var = Core.NVal (Core.Var x) in
      equal_value u_ctx v_ctx (f var) (g var)
    | Eq (a, u, v), Eq (b, w, x) ->
      equal_value u_ctx v_ctx a b
      && Core.equal_value u w && Core.equal_value v x
    | Thunk t, Thunk s -> equal_comp u_ctx v_ctx t s
    | Var x, Var y ->
      let x_ty = SMap.find x u_ctx.ty_ctx in
      let y_ty = SMap.find y v_ctx.ty_ctx in
      equal_value u_ctx v_ctx x_ty y_ty
      &&
      let x_val = SMap.find x u_ctx.env.values in
      let y_val = SMap.find y v_ctx.env.values in
      Core.equal_value x_val y_val
    | Pair (u, v), Pair (w, x) ->
      equal_value u_ctx v_ctx u w && equal_value u_ctx v_ctx v x
    | Int i, Int j -> i = j
    | IntTy, IntTy -> true
    | Refl, Refl -> true
    | Symbol s, Symbol t -> s = t
    | SymbolSet ss, SymbolSet ts -> SymbolSet.equal ss ts
    | _ -> false

  and equal_comp a_ctx b_ctx a b =
    match a, b with
    | CompUniv u, CompUniv w ->
      DeptyZ3.set_eq_univ a_ctx.z3_ctx u w;
      true
    | F a, F b | Force a, Force b | Return a, Return b ->
      equal_value a_ctx b_ctx a b
    | Pi (xs, f), Pi (ys, g) -> begin
      let check_types (x, t) (_, s) =
        if equal_value a_ctx b_ctx t s then
          Core.NVal (Core.Var x)
        else
          raise Exit
      in
      try
        let vars = List.map2 check_types xs ys in
        let f', fx = f vars in
        let g', fx' = g vars in
        equal_comp a_ctx b_ctx f' g'
        &&
        (DeptyZ3.set_eq_fx a_ctx.z3_ctx fx fx';
         true)
      with Exit -> false
    end
    | Lam (xs, f), Lam (ys, g) -> begin
      let check_types (x, t) (_, s) =
        if equal_value a_ctx b_ctx t s then
          Core.NVal (Core.Var x)
        else
          raise Exit
      in
      try
        let vars = List.map2 check_types xs ys in
        equal_comp a_ctx b_ctx (f vars) (g vars)
      with Exit -> false
    end
    | Let (x, a, t, u), Let (y, b, s, v)
    | DLet (x, a, t, u), DLet (y, b, s, v) ->
      equal_value a_ctx b_ctx a b
      && equal_comp a_ctx b_ctx t s
      &&
      let var = Core.NVal (Core.Var x) in
      equal_comp
        (add_ty (add_val a_ctx x var) x a)
        (add_ty (add_val b_ctx y var) y b)
        u v
    | RecSigma (v, m, t), RecSigma (u, n, s)
    | RecEq (v, m, t), RecEq (u, n, s) ->
      equal_value a_ctx b_ctx v u
      && equal_comp a_ctx b_ctx m n
      && equal_comp a_ctx b_ctx t s
    | RecSym (v, m, ts), RecSym (u, n, ss) ->
      equal_value a_ctx b_ctx v u
      && equal_comp a_ctx b_ctx m n
      && SymbolMap.equal (equal_comp a_ctx b_ctx) ts ss
    | Add (u, v), Add (w, x) ->
      equal_value a_ctx b_ctx u w && equal_value a_ctx b_ctx v x
    | _ -> false

  let equal_value ctx = equal_value ctx ctx
  let equal_comp ctx = equal_comp ctx ctx

  exception TypeError

  let err_unless b =
    if not b then
      raise TypeError

  let rec check_value (ctx : context) (ty : value_ty)
      (v : Syntax.value_ty) : bool =
    (* This assumes that ty is always well formed *)
    match v, ty with
    | Syntax.ValUniv i, ValUniv j ->
      let j' = DeptyZ3.mk_const_univ ctx.z3_ctx (i + 1) in
      DeptyZ3.set_eq_univ ctx.z3_ctx j j';
      true
    | Syntax.U (es, x), ValUniv i ->
      check_comp ctx (CompUniv i)
        (DeptyZ3.mk_const_fx ctx.z3_ctx es)
        x
    | Syntax.Pair (u, v), Sigma (_, a, b) ->
      check_value ctx a u
      && check_value ctx (b (Core.resolve ctx.env u)) v
    | Syntax.Symbol s, SymbolSet ss -> SymbolSet.mem s ss
    | Syntax.Sigma (x, a, b), ValUniv k ->
      let i = DeptyZ3.mk_var_univ ctx.z3_ctx in
      check_value ctx (ValUniv i) a
      &&
      let ctx' =
        {
          ctx with
          ty_ctx =
            SMap.add x (from_syntax_value ctx a) ctx.ty_ctx;
        }
      in
      let j = DeptyZ3.mk_var_univ ctx'.z3_ctx in
      check_value ctx' (ValUniv j) b
      &&
      let k' = DeptyZ3.mk_max_univ ctx.z3_ctx i j in
      DeptyZ3.set_eq_univ ctx.z3_ctx k k';
      true
    | Syntax.Eq (a, v, w), ValUniv i ->
      check_value ctx (ValUniv i) a
      &&
      let a' = from_syntax_value ctx a in
      check_value ctx a' v && check_value ctx a' w
    | Syntax.Refl, Eq (_, v, w) -> Core.equal_value v w
    | Syntax.Int _, IntTy -> true
    | v, ty ->
      let ty' = infer_value ctx v in
      equal_value ctx ty ty'

  and check_comp (ctx : context) (ty : comp_ty)
      (es : DeptyZ3.fx) (c : Syntax.comp_ty) : bool =
    match c, ty with
    | Syntax.CompUniv i, CompUniv j ->
      let j' = DeptyZ3.mk_const_univ ctx.z3_ctx (i + 1) in
      DeptyZ3.set_eq_univ ctx.z3_ctx j j';
      true
    | Syntax.F a, CompUniv i -> check_value ctx (ValUniv i) a
    | c, ty ->
      let ty', fs = infer_comp ctx c in
      equal_comp ctx ty ty'
      &&
      (DeptyZ3.set_lte_fx ctx.z3_ctx es fs;
       true)

  and infer_value (ctx : context) : Syntax.value -> value_ty =
    function
    | Syntax.Var x -> SMap.find x ctx.ty_ctx
    | Syntax.ValUniv i ->
      ValUniv (DeptyZ3.mk_const_univ ctx.z3_ctx (i + 1))
    | Syntax.IntTy ->
      ValUniv (DeptyZ3.mk_const_univ ctx.z3_ctx 1)
    | Syntax.Int _ -> IntTy
    | Syntax.U (es, x) ->
      let i = DeptyZ3.mk_var_univ ctx.z3_ctx in
      if
        check_comp ctx (CompUniv i)
          (DeptyZ3.mk_const_fx ctx.z3_ctx es)
          x
      then
        ValUniv i
      else
        raise TypeError
    | Syntax.Thunk t ->
      let t, es = infer_comp ctx t in
      U (es, t)
    | ( Syntax.Refl
      | Syntax.Pair (_, _)
      | Syntax.Symbol _ | Syntax.Sigma _ | Syntax.Eq _ ) as v ->
      Fmt.pf Fmt.stderr "don't know how to infer value %a"
        Syntax.Pretty.pp_value v;
      raise TypeError
    | Syntax.SymbolSet _ ->
      ValUniv (DeptyZ3.mk_const_univ ctx.z3_ctx 1)

  and infer_comp (ctx : context) :
      Syntax.comp -> comp_ty * DeptyZ3.fx = function
    | Syntax.CompUniv i ->
      ( CompUniv (DeptyZ3.mk_const_univ ctx.z3_ctx (i + 1)),
        DeptyZ3.mk_pure_fx ctx.z3_ctx )
    | Syntax.F a -> begin
      match infer_value ctx a with
      | ValUniv i -> CompUniv i, DeptyZ3.mk_pure_fx ctx.z3_ctx
      | _ -> raise TypeError
    end
    | Syntax.Pi (xs, t) ->
      let folder (u_max, ctx) (x, ty) =
        let u = DeptyZ3.mk_var_univ ctx.z3_ctx in
        err_unless (check_value ctx (ValUniv u) ty);
        let ty' = from_syntax_value ctx ty in
        ( DeptyZ3.mk_max_univ ctx.z3_ctx u u_max,
          {ctx with ty_ctx = SMap.add x ty' ctx.ty_ctx} )
      in
      let u = DeptyZ3.mk_var_univ ctx.z3_ctx in
      let u_max, ctx' = List.fold_left folder (u, ctx) xs in
      let fx = DeptyZ3.mk_var_fx ctx.z3_ctx in
      err_unless (check_comp ctx' (CompUniv u) fx t);
      CompUniv u_max, fx
    | Syntax.Force v -> begin
      match infer_value ctx v with
      | U (e, x) -> x, e
      | _ -> raise TypeError
    end
    | Syntax.Return v ->
      ( F (infer_value ctx v),
        (* Return is a terminal so it must be pure *)
        DeptyZ3.mk_pure_fx ctx.z3_ctx )
    | Syntax.Let (x, a, t, u) ->
      let a' = from_syntax_value ctx a in
      let fx = DeptyZ3.mk_var_fx ctx.z3_ctx in
      if check_comp ctx (F a') fx t then
        let ty, fx' =
          infer_comp
            {ctx with ty_ctx = SMap.add x a' ctx.ty_ctx}
            u
        in
        ty, DeptyZ3.mk_union_fx ctx.z3_ctx fx fx'
      else
        raise TypeError
    | Syntax.DLet (x, a, t, u) ->
      let a' = from_syntax_value ctx a in
      let fx = DeptyZ3.mk_var_fx ctx.z3_ctx in
      if check_comp ctx (F a') fx t then
        let ctx' =
          {ctx with ty_ctx = SMap.add x a' ctx.ty_ctx}
        in
        let ty, fx' = infer_comp ctx' u in
        ( Let (x, a', from_syntax_comp ctx' t, ty),
          DeptyZ3.mk_union_fx ctx.z3_ctx fx fx' )
      else
        raise TypeError
    | Syntax.Lam (xs, t) ->
      let folder ctx (x, ty) =
        let u = DeptyZ3.mk_var_univ ctx.z3_ctx in
        err_unless (check_value ctx (ValUniv u) ty);
        let ty' = from_syntax_value ctx ty in
        {ctx with ty_ctx = SMap.add x ty' ctx.ty_ctx}, (x, ty')
      in
      let ctx', xs = List.fold_left_map folder ctx xs in
      let t' vs =
        let folder ctx (x, _) v = add_val ctx x v in
        let ctx'' = List.fold_left2 folder ctx' xs vs in
        infer_comp ctx'' t
      in
      Pi (xs, t'), DeptyZ3.mk_var_fx ctx.z3_ctx
    | Syntax.App (t, vs) -> begin
      match infer_comp ctx t with
      | Pi (xs, t), fx
        when List.for_all2
               (fun (_, a) v -> check_value ctx a v)
               xs vs ->
        let ty, fx' = t (List.map (Core.resolve ctx.env) vs) in
        ty, DeptyZ3.mk_union_fx ctx.z3_ctx fx fx'
      | _ -> raise TypeError
    end
    | Syntax.RecSym (v, x, ts) ->
      let ss =
        SymbolMap.to_list ts |> List.map fst
        |> SymbolSet.of_list
      in
      let ss = SymbolSet ss in
      err_unless (check_value ctx ss v);
      let u = DeptyZ3.mk_var_univ ctx.z3_ctx in
      (* The motive should be effectualy pure *)
      let m_fx = DeptyZ3.mk_pure_fx ctx.z3_ctx in
      err_unless
        (check_comp ctx
           (Pi (["_", ss], fun _ -> CompUniv u, m_fx))
           m_fx x);
      let x = Core.reduce ctx.env x in
      let x vs =
        Core.apply x vs |> Core.quote_comp
        |> from_syntax_comp ctx
      in
      (* Assuming all branches have the same effect.
         Alternatively we could:
         - collect the effects of each branch and union them together
         - introduce first class effects and have an "effect motive" *)
      let b_fx = DeptyZ3.mk_var_fx ctx.z3_ctx in
      err_unless
        begin
          let check_branch s t =
            check_comp ctx (x [Core.Symbol s]) b_fx t
          in
          SymbolMap.for_all check_branch ts
        end;
      x [Core.resolve ctx.env v], b_fx
    | Syntax.RecEq (v, x, t) -> begin
      match infer_value ctx v with
      | Eq (a, w1, w2) ->
        let x_domain y =
          match y with
          | [y] -> Eq (a, w1, y)
          | _ -> raise TypeError
        in
        let u = DeptyZ3.mk_var_univ ctx.z3_ctx in
        (* motive is effectually pure *)
        let pure = DeptyZ3.mk_pure_fx ctx.z3_ctx in
        let x_ty =
          Pi
            ( ["y", a],
              fun y ->
                ( Pi
                    ( ["_", x_domain y],
                      fun _ -> CompUniv u, pure ),
                  pure ) )
        in
        err_unless (check_comp ctx x_ty pure x);
        let x = Core.reduce ctx.env x in
        let x vs =
          Core.apply x vs |> Core.quote_comp
          |> from_syntax_comp ctx
        in
        err_unless (check_comp ctx (x [w1; Refl]) pure t);
        x [w2; Core.resolve ctx.env v], pure
      | _ -> raise TypeError
    end
    | Syntax.RecSigma (v, x, t) -> begin
      match infer_value ctx v with
      | Sigma (_, a, b) as d ->
        let u = DeptyZ3.mk_var_univ ctx.z3_ctx in
        (* motive is effectually pure *)
        let x_fx = DeptyZ3.mk_pure_fx ctx.z3_ctx in
        err_unless
          (check_comp ctx
             (Pi (["_", d], fun _ -> CompUniv u, x_fx))
             x_fx x);
        let x = Core.reduce ctx.env x in
        let x vs =
          Core.apply x vs |> Core.quote_comp
          |> from_syntax_comp ctx
        in
        let fx = DeptyZ3.mk_var_fx ctx.z3_ctx in
        err_unless
          begin
            check_comp ctx
              (Pi
                 ( ["x", a; "y", b (Core.NVal (Core.Var "x"))],
                   fun v ->
                     match v with
                     | [x'; y'] -> x [Core.Pair (x', y')], x_fx
                     | _ -> raise TypeError ))
              fx t
          end;
        x [Core.resolve ctx.env v], fx
      | _ -> raise TypeError
    end
    | Syntax.Add (u, v) ->
      if check_value ctx IntTy u && check_value ctx IntTy v then
        F IntTy, DeptyZ3.mk_pure_fx ctx.z3_ctx
      else
        raise TypeError
    | Syntax.Do e ->
      let fx = DeptyZ3.mk_singleton_fx ctx.z3_ctx e in
      let env, t = SMap.find e ctx.env.handlers in
      let ty, fx' = infer_comp {ctx with env} t in
      DeptyZ3.set_lte_fx ctx.z3_ctx fx' fx;
      ty, fx
    | Syntax.Handle (e, a, b) ->
      let handlers = SMap.add e (ctx.env, a) ctx.env.handlers in
      let a_ty, a_fx = infer_comp ctx a in
      (* Not sure what we should do with a_fx *)
      ignore a_fx;
      let handler_ty_ctx = SMap.add e a_ty ctx.handler_ty_ctx in
      let b_ty, b_fx =
        infer_comp
          {
            ctx with
            handler_ty_ctx;
            env = {ctx.env with handlers};
          }
          b
      in
      b_ty, DeptyZ3.mk_remove_fx ctx.z3_ctx b_fx e
end

let hello = "hello"
