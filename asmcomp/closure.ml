(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Introduction of closures, uncurrying, recognition of direct calls *)

open Misc
open Asttypes
open Primitive
open Lambda
open Switch
open Clambda
open Debuginfo

(* Auxiliaries for compiling functions *)

let rec split_list n l =
  if n <= 0 then ([], l) else begin
    match l with
      [] -> fatal_error "Closure.split_list"
    | a::l -> let (l1, l2) = split_list (n-1) l in (a::l1, l2)
  end

let rec build_closure_env env_param pos = function
    [] -> Tbl.empty
  | id :: rem ->
    let ul = mk(Uprim(Pfield pos, [mk(Uvar env_param)])) in
    Tbl.add id ul (build_closure_env env_param (pos+1) rem)

(* Auxiliary for accessing globals.  We change the name of the global
   to the name of the corresponding asm symbol.  This is done here
   and no longer in Cmmgen so that approximations stored in .cmx files
   contain the right names if the -for-pack option is active. *)

let getglobal id =
  let symb = Ident.create_persistent (Compilenv.symbol_for_global id) in
  mk(Uprim(Pgetglobal symb, []))


(* Check if a variable occurs in a [clambda] term. *)

let occurs_var var u =
  let rec occurs ul = match ul.exp with
      Uvar v -> v = var
    | Uconst (cst,_) -> false
    | Udirect_apply(lbl, args) -> List.exists occurs args
    | Ugeneric_apply(funct, args) -> occurs funct || List.exists occurs args
    | Uclosure(fundecls, clos) -> List.exists occurs clos
    | Uoffset(u, ofs) -> occurs u
    | Ulet(id, def, body) -> occurs def || occurs body
    | Uletrec(decls, body) ->
        List.exists (fun (id, u) -> occurs u) decls || occurs body
    | Uprim(p, args) -> List.exists occurs args
    | Uswitch(arg, s) ->
        occurs arg ||
        occurs_array s.us_actions_consts || occurs_array s.us_actions_blocks
    | Ustaticfail (_, args) -> List.exists occurs args
    | Ucatch(_, _, body, hdlr) -> occurs body || occurs hdlr
    | Utrywith(body, exn, hdlr) -> occurs body || occurs hdlr
    | Uifthenelse(cond, ifso, ifnot) ->
        occurs cond || occurs ifso || occurs ifnot
    | Usequence(u1, u2) -> occurs u1 || occurs u2
    | Uwhile(cond, body) -> occurs cond || occurs body
    | Ufor(id, lo, hi, dir, body) -> occurs lo || occurs hi || occurs body
    | Uassign(id, u) -> id = var || occurs u
    | Usend(_, met, obj, args) ->
        occurs met || occurs obj || List.exists occurs args
  and occurs_array a =
    try
      for i = 0 to Array.length a - 1 do
        if occurs a.(i) then raise Exit
      done;
      false
    with Exit ->
      true
  in occurs u

(* Determine whether the estimated size of a clambda term is below
   some threshold *)

let prim_size prim args =
  match prim with
    Pidentity -> 0
  | Pgetglobal id -> 1
  | Psetglobal id -> 1
  | Pmakeblock(tag, mut) -> 5 + List.length args
  | Pfield f -> 1
  | Psetfield(f, isptr) -> if isptr then 4 else 1
  | Pfloatfield f -> 1
  | Psetfloatfield f -> 1
  | Pduprecord _ -> 10 + List.length args
  | Pccall p -> (if p.prim_alloc then 10 else 4) + List.length args
  | Praise -> 4
  | Pstringlength -> 5
  | Pstringrefs | Pstringsets -> 6
  | Pmakearray kind -> 5 + List.length args
  | Parraylength kind -> if kind = Pgenarray then 6 else 2
  | Parrayrefu kind -> if kind = Pgenarray then 12 else 2
  | Parraysetu kind -> if kind = Pgenarray then 16 else 4
  | Parrayrefs kind -> if kind = Pgenarray then 18 else 8
  | Parraysets kind -> if kind = Pgenarray then 22 else 10
  | Pbittest -> 3
  | Pbigarrayref(_, ndims, _, _) -> 4 + ndims * 6
  | Pbigarrayset(_, ndims, _, _) -> 4 + ndims * 6
  | _ -> 2 (* arithmetic and comparisons *)

(* Very raw approximation of switch cost *)

let lambda_smaller lam threshold =
  let size = ref 0 in
  let rec lambda_size lam =
    if !size > threshold then raise Exit;
    match lam.exp with
      Uvar v -> ()
    | Uconst(
	(Const_base(Const_int _ | Const_char _ | Const_float _ |
                        Const_int32 _ | Const_int64 _ | Const_nativeint _) |
             Const_pointer _), _) -> incr size
(* Structured Constants are now emitted during closure conversion. *)
    | Uconst (_, Some _) -> incr size
    | Uconst _ ->
        raise Exit (* avoid duplication of structured constants *)
    | Udirect_apply(fn, args) ->
        size := !size + 4; lambda_list_size args
    | Ugeneric_apply(fn, args) ->
        size := !size + 6; lambda_size fn; lambda_list_size args
    | Uclosure(defs, vars) ->
        raise Exit (* inlining would duplicate function definitions *)
    | Uoffset(lam, ofs) ->
        incr size; lambda_size lam
    | Ulet(id, lam, body) ->
        lambda_size lam; lambda_size body
    | Uletrec(bindings, body) ->
        raise Exit (* usually too large *)
    | Uprim(prim, args) ->
        size := !size + prim_size prim args;
        lambda_list_size args
    | Uswitch(lam, cases) ->
        if Array.length cases.us_actions_consts > 1 then size := !size + 5 ;
        if Array.length cases.us_actions_blocks > 1 then size := !size + 5 ;
        lambda_size lam;
        lambda_array_size cases.us_actions_consts ;
        lambda_array_size cases.us_actions_blocks
    | Ustaticfail (_,args) -> lambda_list_size args
    | Ucatch(_, _, body, handler) ->
        incr size; lambda_size body; lambda_size handler
    | Utrywith(body, id, handler) ->
        size := !size + 8; lambda_size body; lambda_size handler
    | Uifthenelse(cond, ifso, ifnot) ->
        size := !size + 2;
        lambda_size cond; lambda_size ifso; lambda_size ifnot
    | Usequence(lam1, lam2) ->
        lambda_size lam1; lambda_size lam2
    | Uwhile(cond, body) ->
        size := !size + 2; lambda_size cond; lambda_size body
    | Ufor(id, low, high, dir, body) ->
        size := !size + 4; lambda_size low; lambda_size high; lambda_size body
    | Uassign(id, lam) ->
        incr size;  lambda_size lam
    | Usend(_, met, obj, args) ->
        size := !size + 8;
        lambda_size met; lambda_size obj; lambda_list_size args
  and lambda_list_size l = List.iter lambda_size l
  and lambda_array_size a = Array.iter lambda_size a in
  try
    lambda_size lam; !size <= threshold
  with Exit ->
    false

(* Check if a clambda term is ``pure'',
   that is without side-effects *and* not containing function definitions *)

let rec is_pure_clambda ul = match ul.exp with
    Uvar v -> true
  | Uconst _ -> true
  | Uprim((Psetglobal _ | Psetfield _ | Psetfloatfield _ | Pduprecord _ |
           Pccall _ | Praise | Poffsetref _ | Pstringsetu | Pstringsets |
           Parraysetu _ | Parraysets _ | Pbigarrayset _), _) -> false
  | Uprim(p, args) -> List.for_all is_pure_clambda args
  | _ -> false

(* Simplify primitive operations on integers *)

let make_const_int dbg n =
  mkdbg dbg (Uconst(Const_base(Const_int n), None)),
  Value_integer n

let make_const_ptr dbg n =
  mkdbg dbg (Uconst(Const_pointer n, None)),
  Value_constptr n

let make_const_bool dbg b =
  make_const_ptr dbg (if b then 1 else 0)

let simplif_prim_pure p (args, approxs) dbg =
  match approxs with
    [Value_integer x] ->
      begin match p with
      | Pidentity    -> make_const_int dbg x
      | Pnegint      -> make_const_int dbg (-x)
      | Poffsetint y -> make_const_int dbg (x + y)
      | _            -> mkdbg dbg (Uprim(p, args)), Value_unknown
      end
  | [Value_integer x; Value_integer y] ->
      begin match p with
      | Paddint -> make_const_int dbg (x + y)
      | Psubint -> make_const_int dbg (x - y)
      | Pmulint -> make_const_int dbg (x * y)
      | Pdivint when y <> 0 -> make_const_int dbg (x / y)
      | Pmodint when y <> 0 -> make_const_int dbg (x mod y)
      | Pandint -> make_const_int dbg (x land y)
      | Porint  -> make_const_int dbg (x lor y)
      | Pxorint -> make_const_int dbg (x lxor y)
      | Plslint -> make_const_int dbg (x lsl y)
      | Plsrint -> make_const_int dbg (x lsr y)
      | Pasrint -> make_const_int dbg (x asr y)
      | Pintcomp cmp ->
          let result = match cmp with
              Ceq -> x = y
            | Cneq -> x <> y
            | Clt -> x < y
            | Cgt -> x > y
            | Cle -> x <= y
            | Cge -> x >= y in
          make_const_bool dbg result
      | _ -> mkdbg dbg (Uprim(p, args)), Value_unknown
      end
  | [Value_constptr x] ->
      begin match p with
        Pidentity -> make_const_ptr dbg x
      | Pnot      -> make_const_bool dbg (x = 0)
      | Pisint    -> make_const_bool dbg true
      | _         -> mkdbg dbg (Uprim(p, args)), Value_unknown
      end
  | [Value_constptr x; Value_constptr y] ->
      begin match p with
        Psequand -> make_const_bool dbg (x <> 0 && y <> 0)
      | Psequor  -> make_const_bool dbg (x <> 0 || y <> 0)
      | _ -> mkdbg dbg (Uprim(p, args)), Value_unknown
      end
  | _ ->
      mkdbg dbg (Uprim(p, args)), Value_unknown

let simplif_prim p (args, approxs as args_approxs) dbg =
  if List.for_all is_pure_clambda args
  then simplif_prim_pure p args_approxs dbg
  else (mkdbg dbg (Uprim(p, args)), Value_unknown)

(* Substitute variables in a [ulambda] term (a body of an inlined function)
   and perform some more simplifications on integer primitives.
   Also perform alpha-conversion on let-bound identifiers to avoid
   clashes with locally-generated identifiers.
   The variables must not be assigned in the term.
   This is used to substitute "trivial" arguments for parameters
   during inline expansion, and also for the translation of let rec
   over functions. *)

let approx_ulam ulam = match ulam.exp with
    Uconst(Const_base(Const_int n),_) -> Value_integer n
  | Uconst(Const_base(Const_char c),_) -> Value_integer(Char.code c)
  | Uconst(Const_pointer n,_) -> Value_constptr n
  | _ -> Value_unknown

let rec substitute sb ulam =
  let mk = mkdbg ulam.dbg in
  match ulam.exp with
    Uvar v ->
      begin
        try { (Tbl.find v sb) with dbg =  ulam.dbg }
        with Not_found -> ulam
      end
  | Uconst _ -> ulam
  | Udirect_apply(lbl, args) ->
      mk (Udirect_apply(lbl, List.map (substitute sb) args))
  | Ugeneric_apply(fn, args) ->
      mk (Ugeneric_apply(substitute sb fn, List.map (substitute sb) args))
  | Uclosure(defs, env) ->
      (* Question: should we rename function labels as well?  Otherwise,
         there is a risk that function labels are not globally unique.
         This should not happen in the current system because:
         - Inlined function bodies contain no Uclosure nodes
           (cf. function [lambda_smaller])
         - When we substitute offsets for idents bound by let rec
           in [close], case [Lletrec], we discard the original
           let rec body and use only the substituted term. *)
      mk (Uclosure(defs, List.map (substitute sb) env))
  | Uoffset(u, ofs) -> mk (Uoffset(substitute sb u, ofs))
  | Ulet(id, u1, u2) ->
      let id' = Ident.rename id in
      mk (Ulet(id', substitute sb u1, substitute (Tbl.add id (mk (Uvar id')) sb) u2))
  | Uletrec(bindings, body) ->
      let bindings1 =
        List.map (fun (id, rhs) -> (id, Ident.rename id, rhs)) bindings in
      let sb' =
        List.fold_right
          (fun (id, id', _) s -> Tbl.add id (mk (Uvar id')) s)
          bindings1 sb in
      mk (Uletrec(
        List.map (fun (id, id', rhs) -> (id', substitute sb' rhs)) bindings1,
        substitute sb' body))
  | Uprim(p, args) ->
      let sargs = List.map (substitute sb) args in
      let (res, _) = simplif_prim p (sargs, List.map approx_ulam sargs) ulam.dbg in
      res
  | Uswitch(arg, sw) ->
      mk (Uswitch(substitute sb arg,
              { sw with
                us_actions_consts =
                  Array.map (substitute sb) sw.us_actions_consts;
                us_actions_blocks =
                  Array.map (substitute sb) sw.us_actions_blocks;
               }))
  | Ustaticfail (nfail, args) ->
      mk (Ustaticfail (nfail, List.map (substitute sb) args))
  | Ucatch(nfail, ids, u1, u2) ->
      mk (Ucatch(nfail, ids, substitute sb u1, substitute sb u2))
  | Utrywith(u1, id, u2) ->
      let id' = Ident.rename id in
      mk (Utrywith(substitute sb u1, id', substitute (Tbl.add id (mk (Uvar id')) sb) u2))
  | Uifthenelse(u1, u2, u3) ->
      let su1 = substitute sb u1 in
      begin match su1.exp with
        Uconst(Const_pointer n, _) ->
          if n <> 0 then substitute sb u2 else substitute sb u3
      | _ ->
          mk (Uifthenelse(su1, substitute sb u2, substitute sb u3))
      end
  | Usequence(u1, u2) -> mk (Usequence(substitute sb u1, substitute sb u2))
  | Uwhile(u1, u2) -> mk (Uwhile(substitute sb u1, substitute sb u2))
  | Ufor(id, u1, u2, dir, u3) ->
      let id' = Ident.rename id in
      mk (Ufor(id', substitute sb u1, substitute sb u2, dir,
           substitute (Tbl.add id (mk (Uvar id')) sb) u3))
  | Uassign(id, u) ->
      let id' =
        try
          match Tbl.find id sb with {exp=Uvar i} -> i | _ -> assert false
        with Not_found ->
          id in
      mk (Uassign(id', substitute sb u))
  | Usend(k, u1, u2, ul) ->
      mk (Usend(k, substitute sb u1, substitute sb u2, List.map (substitute sb) ul))

(* Perform an inline expansion *)

let is_simple_argument ulam = match ulam.exp with
    Uvar _ -> true
  | Uconst(Const_base(Const_int _ | Const_char _ | Const_float _ |
                      Const_int32 _ | Const_int64 _ | Const_nativeint _),_) ->
      true
  | Uconst(Const_pointer _, _) -> true
  | _ -> false

let no_effects ulam = match ulam.exp with
    Uclosure _ -> true
  | Uconst(Const_base(Const_string _),_) -> true
  | _ -> is_simple_argument ulam

let rec bind_params_rec subst params args body =
  match (params, args) with
    ([], []) -> substitute subst body
  | (p1 :: pl, a1 :: al) ->
      if is_simple_argument a1 then
        bind_params_rec (Tbl.add p1 a1 subst) pl al body
      else begin
        let p1' = Ident.rename p1 in
        let mk = mkdbg body.dbg in
        let body' =
          bind_params_rec (Tbl.add p1 (mk (Uvar p1')) subst) pl al body in
        if occurs_var p1 body then mk (Ulet(p1', a1, body'))
        else if no_effects a1 then
          body'
        else
          mk (Usequence(a1, body'))
      end
  | (_, _) -> assert false

let bind_params params args body =
  (* Reverse parameters and arguments to preserve right-to-left
     evaluation order (PR#2910). *)
  bind_params_rec Tbl.empty (List.rev params) (List.rev args) body

(* Check if a lambda term is ``pure'',
   that is without side-effects *and* not containing function definitions *)

let rec is_pure = function
    Lvar v -> true
  | Lconst cst -> true
  | Lprim((Psetglobal _ | Psetfield _ | Psetfloatfield _ | Pduprecord _ |
           Pccall _ | Praise | Poffsetref _ | Pstringsetu | Pstringsets |
           Parraysetu _ | Parraysets _ | Pbigarrayset _), _) -> false
  | Lprim(p, args) -> List.for_all is_pure args
  | Levent(lam, ev) -> is_pure lam
  | _ -> false

(* Generate a direct application *)

let direct_apply fundesc funct ufunct uargs =
  let mk = mkdbg ufunct.dbg in
  let app_args =
    if fundesc.fun_closed then uargs else uargs @ [ufunct] in
  let app =
    match fundesc.fun_inline with
      None -> mk (Udirect_apply(fundesc.fun_label, app_args))
    | Some(params, body) -> bind_params params app_args body in
  (* If ufunct can contain side-effects or function definitions,
     we must make sure that it is evaluated exactly once.
     If the function is not closed, we evaluate ufunct as part of the
     arguments.
     If the function is closed, we force the evaluation of ufunct first. *)
  if not fundesc.fun_closed || is_pure funct
  then app
  else mk (Usequence(ufunct, app))

(* Add [Value_integer] or [Value_constptr] info to the approximation
   of an application *)

let strengthen_approx appl approx =
  match approx_ulam appl with
    (Value_integer _ | Value_constptr _) as intapprox -> intapprox
  | _ -> approx

(* If a term has approximation Value_integer or Value_constptr and is pure,
   replace it by an integer constant *)

let check_constant_result lam ulam approx =
  match approx with
    Value_integer n when is_pure lam -> make_const_int ulam.dbg n
  | Value_constptr n when is_pure lam -> make_const_ptr ulam.dbg n
  | _ -> (ulam, approx)

(* Evaluate an expression with known value for its side effects only,
   or discard it if it's pure *)

let sequence_constant_expr lam ulam1 (ulam2, approx2 as res2) =
  if is_pure lam then res2 else (mk(Usequence(ulam1, ulam2)), approx2)

(* Maintain the approximation of the global structure being defined *)

let global_approx = ref([||] : value_approximation array)

(* Maintain the nesting depth for functions *)

let function_nesting_depth = ref 0
let excessive_function_nesting_depth = 5

(* Decorate clambda term with debug information *)

let rec add_debug_info ev u =
  match ev.lev_kind with
  | Lev_after _ ->
      begin match u.exp with
      | Udirect_apply _
      | Ugeneric_apply _
      | Uprim _
      | Usend _ -> { u with dbg = dbg_of_call ev }
      | Usequence(u1,u2) ->
        { u with exp = Usequence(u1, add_debug_info ev u2) }
      | _ -> { u with dbg = dbg_of_event ev }
      end
  | _ -> u

(* Uncurry an expression and explicitate closures.
   Also return the approximation of the expression.
   The approximation environment [fenv] maps idents to approximations.
   Idents not bound in [fenv] approximate to [Value_unknown].
   The closure environment [cenv] maps idents to [ulambda] terms.
   It is used to substitute environment accesses for free identifiers. *)

let close_approx_var fenv cenv id =
  let approx = try Tbl.find id fenv with Not_found -> Value_unknown in
  match approx with
    Value_integer n ->
      make_const_int Debuginfo.none n
  | Value_constptr n ->
      make_const_ptr Debuginfo.none n
  | approx ->
      let subst = try Tbl.find id cenv with Not_found -> mk(Uvar id) in
      (subst, approx)

let close_var fenv cenv id =
  let (ulam, app) = close_approx_var fenv cenv id in ulam

let rec close fenv cenv lam = match lam with
    Lvar id ->
      close_approx_var fenv cenv id
  | Lconst cst ->
      begin match cst with
        Const_base(Const_int n) -> (mk (Uconst (cst,None)), Value_integer n)
      | Const_base(Const_char c) -> (mk (Uconst (cst,None)), Value_integer(Char.code c))
      | Const_pointer n -> (mk (Uconst (cst, None)), Value_constptr n)
      | _ -> (mk (Uconst (cst, Some (Compilenv.new_structured_constant cst true))), Value_unknown)
      end
  | Lfunction(kind, params, body) as funct ->
      close_one_function fenv cenv (Ident.create "fun") funct

    (* We convert [f a] to [let a' = a in fun b c -> f a' b c] 
       when fun_arity > nargs *)
  | Lapply(funct, args) ->
      let nargs = List.length args in
      begin match (close fenv cenv funct, close_list fenv cenv args) with
        ((ufunct, Value_closure(fundesc, approx_res)),
         [{exp=Uprim(Pmakeblock(_, _), uargs)}])
        when List.length uargs = - fundesc.fun_arity ->
          let app = direct_apply fundesc funct ufunct uargs in
          (app, strengthen_approx app approx_res)

      | ((ufunct, Value_closure(fundesc, approx_res)), uargs)
        when nargs = fundesc.fun_arity ->
          let app = direct_apply fundesc funct ufunct uargs in
          (app, strengthen_approx app approx_res)

      | ((ufunct, Value_closure(fundesc, approx_res)), uargs)
          when nargs < fundesc.fun_arity ->
	let first_args = List.map (fun arg ->
	  (Ident.create "arg", arg) ) uargs in
	let final_args = Array.to_list (Array.init (fundesc.fun_arity - nargs) (fun _ ->
	  Ident.create "arg")) in
	let rec iter args body =
	  match args with
	      [] -> body
	    | (arg1, arg2) :: args ->
	      iter args (mk (Ulet ( arg1, arg2, body)))
	in
	let internal_args =
	  (List.map (fun (arg1, arg2) -> Lvar arg1) first_args)
	  @ (List.map (fun arg -> Lvar arg ) final_args)
	in
	let (new_fun, approx) = close fenv cenv
	  (Lfunction(
	    Curried, final_args, Lapply(funct, internal_args)))
	in
	let new_fun = iter first_args new_fun in
	(new_fun, approx)

      | ((ufunct, Value_closure(fundesc, approx_res)), uargs)
        when fundesc.fun_arity > 0 && nargs > fundesc.fun_arity ->
          let (first_args, rem_args) = split_list fundesc.fun_arity uargs in
          mk (Ugeneric_apply(direct_apply fundesc funct ufunct first_args, rem_args)),
          Value_unknown
      | ((ufunct, _), uargs) -> mk (Ugeneric_apply(ufunct, uargs)), Value_unknown
      end
  | Lsend(kind, met, obj, args) ->
      let (umet, _) = close fenv cenv met in
      let (uobj, _) = close fenv cenv obj in
      mk (Usend(kind, umet, uobj, close_list fenv cenv args)), Value_unknown
  | Llet(str, id, lam, body) ->
      let (ulam, alam) = close_named fenv cenv id lam in
      begin match (str, alam) with
        (Variable, _) ->
          let (ubody, abody) = close fenv cenv body in
          mk (Ulet(id, ulam, ubody)), abody
      | (_, (Value_integer _ | Value_constptr _))
        when str = Alias || is_pure lam ->
          close (Tbl.add id alam fenv) cenv body
      | (_, _) ->
          let (ubody, abody) = close (Tbl.add id alam fenv) cenv body in
          mk (Ulet(id, ulam, ubody)), abody
      end
  | Lletrec(defs, body) ->
      if List.for_all
           (function (id, Lfunction(_, _, _)) -> true | _ -> false)
           defs
      then begin
        (* Simple case: only function definitions *)
        let (clos, infos) = close_functions fenv cenv defs in
        let clos_ident = Ident.create "clos" in
        let fenv_body =
          List.fold_right
            (fun (id, pos, approx) fenv -> Tbl.add id approx fenv)
            infos fenv in
        let (ubody, approx) = close fenv_body cenv body in
        let sb =
          List.fold_right
            (fun (id, pos, approx) sb ->
              Tbl.add id (mk (Uoffset(mk (Uvar clos_ident), pos))) sb)
            infos Tbl.empty in
        mk (Ulet(clos_ident, clos, substitute sb ubody)), approx
      end else begin
        (* General case: recursive definition of values *)
        let rec clos_defs = function
          [] -> ([], fenv)
        | (id, lam) :: rem ->
            let (udefs, fenv_body) = clos_defs rem in
            let (ulam, approx) = close fenv cenv lam in
            ((id, ulam) :: udefs, Tbl.add id approx fenv_body) in
        let (udefs, fenv_body) = clos_defs defs in
        let (ubody, approx) = close fenv_body cenv body in
        mk (Uletrec(udefs, ubody)), approx
      end
  | Lprim(Pgetglobal id, []) ->
      check_constant_result lam
                            (getglobal id)
                            (Compilenv.global_approx id)
  | Lprim(Pmakeblock(tag, mut) as prim, lams) ->
      let (ulams, approxs) = List.split (List.map (close fenv cenv) lams) in
      mk (Uprim(prim, ulams)),
       begin match mut with
           Immutable -> Value_tuple(Array.of_list approxs)
         | Mutable -> Value_unknown
       end
  | Lprim(Pfield n, [lam]) ->
      let (ulam, approx) = close fenv cenv lam in
      let fieldapprox =
        match approx with
          Value_tuple a when n < Array.length a -> a.(n)
        | _ -> Value_unknown in
      check_constant_result lam (mk (Uprim(Pfield n, [ulam]))) fieldapprox
  | Lprim(Psetfield(n, _), [Lprim(Pgetglobal id, []); lam]) ->
      let (ulam, approx) = close fenv cenv lam in
      (!global_approx).(n) <- approx;
      mk (Uprim(Psetfield(n, false), [getglobal id; ulam])), Value_unknown
  | Lprim(Praise, [Levent(arg, ev)]) ->
      let (ulam, approx) = close fenv cenv arg in
      mkdbg (dbg_of_raise ev)(Uprim(Praise, [ulam])),
      Value_unknown
  | Lprim(p, args) ->
      simplif_prim p (close_list_approx fenv cenv args) none
  | Lswitch(arg, sw) ->
(* NB: failaction might get copied, thus it should be some Lstaticraise *)
      let (uarg, _) = close fenv cenv arg in
      let const_index, const_actions =
        close_switch fenv cenv sw.sw_consts sw.sw_numconsts sw.sw_failaction
      and block_index, block_actions =
        close_switch fenv cenv sw.sw_blocks sw.sw_numblocks sw.sw_failaction in
      mk (Uswitch(uarg,
               {us_index_consts = const_index;
                us_actions_consts = const_actions;
                us_index_blocks = block_index;
                us_actions_blocks = block_actions})),
      Value_unknown
  | Lstaticraise (i, args) ->
      mk (Ustaticfail (i, close_list fenv cenv args)), Value_unknown
  | Lstaticcatch(body, (i, vars), handler) ->
      let (ubody, _) = close fenv cenv body in
      let (uhandler, _) = close fenv cenv handler in
      mk (Ucatch(i, vars, ubody, uhandler)), Value_unknown
  | Ltrywith(body, id, handler) ->
      let (ubody, _) = close fenv cenv body in
      let (uhandler, _) = close fenv cenv handler in
      mk (Utrywith(ubody, id, uhandler)), Value_unknown
  | Lifthenelse(arg, ifso, ifnot) ->
      begin match close fenv cenv arg with
        (uarg, Value_constptr n) ->
          sequence_constant_expr arg uarg
            (close fenv cenv (if n = 0 then ifnot else ifso))
      | (uarg, _ ) ->
          let (uifso, _) = close fenv cenv ifso in
          let (uifnot, _) = close fenv cenv ifnot in
          mk (Uifthenelse(uarg, uifso, uifnot)), Value_unknown
      end
  | Lsequence(lam1, lam2) ->
      let (ulam1, _) = close fenv cenv lam1 in
      let (ulam2, approx) = close fenv cenv lam2 in
      mk (Usequence(ulam1, ulam2)), approx
  | Lwhile(cond, body) ->
      let (ucond, _) = close fenv cenv cond in
      let (ubody, _) = close fenv cenv body in
      mk (Uwhile(ucond, ubody)), Value_unknown
  | Lfor(id, lo, hi, dir, body) ->
      let (ulo, _) = close fenv cenv lo in
      let (uhi, _) = close fenv cenv hi in
      let (ubody, _) = close fenv cenv body in
      mk (Ufor(id, ulo, uhi, dir, ubody)), Value_unknown
  | Lassign(id, lam) ->
      let (ulam, _) = close fenv cenv lam in
      mk (Uassign(id, ulam)), Value_unknown
  | Levent(lam, ev) ->
      let (ulam, approx) = close fenv cenv lam in
      (add_debug_info ev ulam, approx)
  | Lifused _ ->
      assert false

and close_list fenv cenv = function
    [] -> []
  | lam :: rem ->
      let (ulam, _) = close fenv cenv lam in
      ulam :: close_list fenv cenv rem

and close_list_approx fenv cenv = function
    [] -> ([], [])
  | lam :: rem ->
      let (ulam, approx) = close fenv cenv lam in
      let (ulams, approxs) = close_list_approx fenv cenv rem in
      (ulam :: ulams, approx :: approxs)

and close_named fenv cenv id = function
    Lfunction(kind, params, body) as funct ->
      close_one_function fenv cenv id funct
  | lam ->
      close fenv cenv lam

(* Build a shared closure for a set of mutually recursive functions *)

and close_functions fenv cenv fun_defs =
  (* Update and check nesting depth *)
  incr function_nesting_depth;
  let initially_closed =
    !function_nesting_depth < excessive_function_nesting_depth in
  (* Determine the free variables of the functions *)
  let fv =
    IdentSet.elements (free_variables (Lletrec(fun_defs, lambda_unit))) in
  (* Build the function descriptors for the functions.
     Initially all functions are assumed not to need their environment
     parameter. *)
  let uncurried_defs =
    List.map
      (function
          (id, Lfunction(kind, params, body)) ->
            let label = Compilenv.make_symbol (Some (Ident.unique_name id)) in
            let arity = List.length params in
            let fundesc =
              {fun_label = label;
               fun_arity = (if kind = Tupled then -arity else arity);
               fun_closed = initially_closed;
               fun_inline = None } in
            (id, params, body, fundesc)
        | (_, _) -> fatal_error "Closure.close_functions")
      fun_defs in
  (* Build an approximate fenv for compiling the functions *)
  let fenv_rec =
    List.fold_right
      (fun (id, params, body, fundesc) fenv ->
        Tbl.add id (Value_closure(fundesc, Value_unknown)) fenv)
      uncurried_defs fenv in
  (* Determine the offsets of each function's closure in the shared block *)
  let env_pos = ref (-1) in
  let clos_offsets =
    List.map
      (fun (id, params, body, fundesc) ->
        let pos = !env_pos + 1 in
        env_pos := !env_pos + 1 + (if fundesc.fun_arity <> 1 then 3 else 2);
        pos)
      uncurried_defs in
  let fv_pos = !env_pos in
  (* This reference will be set to false if the hypothesis that a function
     does not use its environment parameter is invalidated. *)
  let useless_env = ref initially_closed in
  (* Translate each function definition *)
  let clos_fundef (id, params, body, fundesc) env_pos =
    let dbg = match body with
      | Levent (_,({lev_kind=Lev_function} as ev)) -> dbg_of_event ev
      | _ -> Debuginfo.none in
    let env_param = Ident.create "env" in
    let cenv_fv =
      build_closure_env env_param (fv_pos - env_pos) fv in
    let cenv_body =
      List.fold_right2
        (fun (id, params, arity, body) pos env ->
          Tbl.add id (mk(Uoffset(mk(Uvar env_param), pos - env_pos))) env)
        uncurried_defs clos_offsets cenv_fv in
    let (ubody, approx) = close fenv_rec cenv_body body in
    if !useless_env && occurs_var env_param ubody then useless_env := false;
    let fun_params = if !useless_env then params else params @ [env_param] in
    ({ uf_dbg    = dbg;
       uf_label  = fundesc.fun_label;
       uf_arity  = fundesc.fun_arity;
       uf_params = fun_params;
       uf_body   = ubody },
     (id, env_pos, Value_closure(fundesc, approx))) in
  (* Translate all function definitions. *)
  let clos_info_list =
    if initially_closed then begin
      let cl = List.map2 clos_fundef uncurried_defs clos_offsets in
      (* If the hypothesis that the environment parameters are useless has been
         invalidated, then set [fun_closed] to false in all descriptions and
         recompile *)
      if !useless_env then cl else begin
        List.iter
          (fun (id, params, body, fundesc) -> fundesc.fun_closed <- false)
          uncurried_defs;
        List.map2 clos_fundef uncurried_defs clos_offsets
      end
    end else
      (* Excessive closure nesting: assume environment parameter is used *)
        List.map2 clos_fundef uncurried_defs clos_offsets
    in
  (* Update nesting depth *)
  decr function_nesting_depth;
  (* Return the Uclosure node and the list of all identifiers defined,
     with offsets and approximations. *)
  let (clos, infos) = List.split clos_info_list in
  mk(Uclosure(clos, List.map (close_var fenv cenv) fv)), infos

(* Same, for one non-recursive function *)

and close_one_function fenv cenv id funct =
  match close_functions fenv cenv [id, funct] with
      (({exp=Uclosure([f], _)} as clos),
       [_, _, (Value_closure(fundesc, _) as approx)]) ->
        (* See if the function can be inlined *)
        if lambda_smaller f.uf_body (!Clflags.inline_threshold + List.length f.uf_params)
        then fundesc.fun_inline <- Some(f.uf_params, f.uf_body);
        (clos, approx)
    | _ -> fatal_error "Closure.close_one_function"

(* Close a switch *)

and close_switch fenv cenv cases num_keys default =
  let index = Array.create num_keys 0
  and store = mk_store Lambda.same in

  (* First default case *)
  begin match default with
  | Some def when List.length cases < num_keys ->
      ignore (store.act_store def)
  | _ -> ()
  end ;
  (* Then all other cases *)
  List.iter
    (fun (key,lam) ->
     index.(key) <- store.act_store lam)
    cases ;
  (* Compile action *)
  let actions =
    Array.map
      (fun lam ->
        let ulam,_ = close fenv cenv lam in
        ulam)
      (store.act_get ()) in
  match actions with
  | [| |] -> [| |], [| |] (* May happen when default is None *)
  | _     -> index, actions


(* The entry point *)

let intro size lam =
  function_nesting_depth := 0;
  global_approx := Array.create size Value_unknown;
  Compilenv.set_global_approx(Value_tuple !global_approx);
  let (ulam, approx) = close Tbl.empty Tbl.empty lam in
  global_approx := [||];
  ulam
