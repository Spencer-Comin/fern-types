type eff = string
type fx = string list

module SymbolSet : module type of Set.Make (String)
module SymbolMap : module type of Map.Make (String)

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

module Pretty : sig
  val pp_comp : comp Fmt.t
  val pp_value : value Fmt.t
end

type type_system = {
  check_type_comp: comp_ty * fx -> comp -> bool;
  infer_type_comp: comp -> comp_ty * fx;
  check_type_value: value_ty -> value -> bool;
  infer_type_value: value -> value_ty;
}

val reduce : comp -> comp
val mk_type_system : fx -> type_system
val equal_comp : comp -> comp -> bool
val equal_value : value -> value -> bool
val hello : string
