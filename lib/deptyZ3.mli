type context

val mk_context : string list -> context

type univ

val mk_var_univ : context -> univ
val mk_const_univ : context -> int -> univ
val mk_max_univ : context -> univ -> univ -> univ
val set_inc_univ : context -> univ -> univ -> unit
val set_eq_univ : context -> univ -> univ -> unit
val univ_to_int : context -> univ -> int

type fx

val mk_var_fx : context -> fx
val mk_pure_fx : context -> fx
val mk_const_fx : context -> string list -> fx
val mk_union_fx : context -> fx -> fx -> fx
val mk_singleton_fx : context -> string -> fx
val mk_remove_fx : context -> fx -> string -> fx
val set_eq_fx : context -> fx -> fx -> unit
val set_lte_fx : context -> fx -> fx -> unit
val fx_to_string_list : context -> fx -> string list
