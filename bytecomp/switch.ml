(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Luc Maranget, projet Moscova, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2000 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Store for actions in object style *)
exception Found of int

type 'a t_store =
    {act_get : unit -> 'a array ; act_store : 'a -> int}

let mk_store same =
  let r_acts = ref [] in
  let store act =
    let rec store_rec i = function
      | [] -> i,[act] 
      | act0::rem ->
          if same act0 act then raise (Found i)
          else
            let i,rem = store_rec (i+1) rem in
            i,act0::rem in
    try
      let i,acts = store_rec 0 !r_acts in
      r_acts := acts ;
      i
    with
    | Found i -> i

  and get () = Array.of_list !r_acts in
  {act_store=store ; act_get=get}



module type S =
 sig
   type primitive
   val eqint : primitive
   val neint : primitive
   val leint : primitive
   val ltint : primitive
   val geint : primitive
   val gtint : primitive
   type act

   val bind : act -> (act -> act) -> act
   val make_offset : act -> int -> act
   val make_prim : primitive -> act list -> act
   val make_isout : act -> act -> act
   val make_isin : act -> act -> act
   val make_if : act -> act -> act -> act
   val make_switch :
      act -> int array -> act array -> act
 end

(* The module will ``produce good code for the case statement'' *)
(*
  Adaptation of
   R.L. Berstein
   ``Producing good code for the case statement''
   Sofware Practice and Experience, 15(10) (1985)
 and
   D.L. Spuler
    ``Two-Way Comparison Search Trees, a Generalisation of Binary Search Trees
      and Split Trees''
    ``Compiler Code Generation for Multiway Branch Statement as
      a Static Search Problem''
   Technical Reports, James Cook University
*)
(*
  Main adaptation is considering interval tests
 (implemented as one addition + one unsigned test and branch)
  which leads to exhaustive search for finding the optimal
  test sequence in small cases and heuristics otherwise.
*)
module Make (Arg : S) =
  struct

    type 'a inter =
        {cases : (int * int * int) array ;
          actions : 'a array}

type 'a t_ctx =  {off : int ; arg : 'a}

let cut = ref 8

let pint chan i =
  if i = min_int then Printf.fprintf chan "-oo"
  else if i=max_int then Printf.fprintf chan "oo"
  else Printf.fprintf chan "%d" i

let pcases chan cases =
  for i =0 to Array.length cases-1 do
    let l,h,act = cases.(i) in
    if l=h then
      Printf.fprintf chan "%d:%d " l act
    else
      Printf.fprintf chan "%a..%a:%d " pint l pint h act
  done

    let prerr_inter i = Printf.fprintf stderr
        "cases=%a" pcases i.cases

let get_act cases i =
  let _,_,r = cases.(i) in
  r
and get_low cases i =
  let r,_,_ = cases.(i) in
  r

type ctests = {
    mutable n : int ;
    mutable ni : int ;
  }

let too_much = {n=max_int ; ni=max_int}

let ptests chan {n=n ; ni=ni } =
  Printf.fprintf chan "{n=%d ; ni=%d }" n ni

let pta chan t =
  for i =0 to Array.length t-1 do
    Printf.fprintf chan "%d: %a\n" i ptests t.(i)
  done

let count_tests s =
  let r =
    Array.init
      (Array.length s.actions)
      (fun _ -> {n=0 ; ni=0 }) in
  let c = s.cases in
  let imax = Array.length c-1 in
  for i=0 to imax do
    let l,h,act = c.(i) in
    let x = r.(act) in
    x.n <- x.n+1 ;
    if l < h && i<> 0 && i<>imax then
      x.ni <- x.ni+1 ;
  done ;
  r


let less_tests c1 c2 =
  if c1.n < c2.n then
    true
  else if c1.n = c2.n then begin
    if c1.ni < c2.ni then
      true
    else
      false
  end else
    false

and eq_tests c1 c2 =
  c1.n = c2.n && c1.ni=c2.ni

let min_tests c1 c2 = if less_tests c1 c2 then c1 else c2

let less2tests (c1,d1) (c2,d2) =
  if eq_tests c1 c2 then
    less_tests d1 d2
  else
    less_tests c1 c2

let add_test t1 t2 =
  t1.n <- t1.n + t2.n ;
  t1.ni <- t1.ni + t2.ni ;

type t_ret = Inter of int * int  | Sep of int | No

let pret chan = function
  | Inter (i,j)-> Printf.fprintf chan "Inter %d %d" i j
  | Sep i -> Printf.fprintf chan "Sep %d" i
  | No -> Printf.fprintf chan "No"

let coupe cases i =
  let l,_,_ = cases.(i) in
  l,
  Array.sub cases 0 i,
  Array.sub cases i (Array.length cases-i)


let case_append c1 c2 =
  let len1 = Array.length c1
  and len2 = Array.length c2 in
  match len1,len2 with
  | 0,_ -> c2
  | _,0 -> c1
  | _,_ ->
      let l1,h1,act1 = c1.(Array.length c1-1)
      and l2,h2,act2 = c2.(0) in
      if act1 = act2 then
        let r = Array.create (len1+len2-1) c1.(0) in
        for i = 0 to len1-2 do
          r.(i) <- c1.(i)
        done ;

        let l =
          if len1-2 >= 0 then begin
            let _,h,_ = r.(len1-2) in
            if h+1 < l1 then
              h+1
            else
              l1
          end else
            l1
        and h =
          if 1 < len2-1 then begin
            let l,_,_ = c2.(1) in
            if h2+1 < l then
              l-1
            else
              h2
          end else
            h2 in
        r.(len1-1) <- (l,h,act1) ;
        for i=1 to len2-1  do
          r.(len1-1+i) <- c2.(i)
        done ;
        r
      else if h1 > l1 then
        let r = Array.create (len1+len2) c1.(0) in
        for i = 0 to len1-2 do
          r.(i) <- c1.(i)
        done ;
        r.(len1-1) <- (l1,l2-1,act1) ;
        for i=0 to len2-1  do
          r.(len1+i) <- c2.(i)
        done ;
        r
      else if h2 > l2 then
        let r = Array.create (len1+len2) c1.(0) in
        for i = 0 to len1-1 do
          r.(i) <- c1.(i)
        done ;
        r.(len1) <- (h1+1,h2,act2) ;
        for i=1 to len2-1  do
          r.(len1+i) <- c2.(i)
        done ;
        r
      else
        Array.append c1 c2


let coupe_inter i j cases =
  let lcases = Array.length cases in
  let low,_,_ = cases.(i)
  and _,high,_ = cases.(j) in
  low,high,
  Array.sub cases i (j-i+1),
  case_append (Array.sub cases 0 i) (Array.sub cases (j+1) (lcases-(j+1)))

type kind = Kvalue of int | Kinter of int | Kempty 

let pkind chan = function
  | Kvalue i ->Printf.fprintf chan "V%d" i
  | Kinter i -> Printf.fprintf chan "I%d" i
  | Kempty -> Printf.fprintf chan "E"

let rec pkey chan  = function
  | [] -> ()
  | [k] -> pkind chan k
  | k::rem ->
      Printf.fprintf chan "%a %a" pkey rem pkind k

let t = Hashtbl.create 17

let make_key  cases =
  let seen = ref []
  and count = ref 0 in
  let rec got_it act = function
    | [] ->
        seen := (act,!count):: !seen ;
        let r = !count in
        incr count ;
        r
    | (act0,index) :: rem ->
        if act0 = act then 
          index
        else
          got_it act rem in

  let make_one l h act =
    if l=h then
      Kvalue (got_it act !seen)
    else
      Kinter (got_it act !seen) in
  
  let rec make_rec i pl =
    if i < 0 then
      []
    else
      let l,h,act = cases.(i) in
      if pl = h+1 then
        make_one l h act::make_rec (i-1) l
      else
        Kempty::make_one l h act::make_rec (i-1) l in

  let l,h,act = cases.(Array.length cases-1) in
  make_one l h act::make_rec (Array.length cases-2) l 
                       

let same_act t =
  let len = Array.length t in
  let a = get_act t (len-1) in
  let rec do_rec i =
    if i < 0 then true
    else
      let b = get_act t i in
      b=a && do_rec (i-1) in
  do_rec (len-2)


  
let rec opt_count top cases =
  let key = make_key cases in
  try
    let r = Hashtbl.find t key in
    r
  with
  | Not_found ->
      let r =
        let lcases = Array.length cases in
        match lcases with
        | 0 -> assert false
        | _ when same_act cases -> No, ({n=0; ni=0},{n=0; ni=0})
        | _ ->
            if lcases < !cut then
              enum top cases
            else
              heuristic top cases in
      Hashtbl.add t key r ;
      r

and heuristic top cases =
  let lcases = Array.length cases in
  let m = lcases/2 in
  let lim,left,right = coupe cases m in
  let sep,csep =
    let ci = {n=1 ; ni=0}
    and cm = {n=1 ; ni=0}
    and _,(cml,cleft) = opt_count false left
    and _,(cmr,cright) = opt_count false right in
    add_test ci cleft ;
    add_test ci cright ;
    if less_tests cml cmr then
      add_test cm cmr
    else
      add_test cm cml ;
    Sep m,(cm, ci)
  and inter,cinter =
    let _,_,act0 = cases.(0)
    and _,_,act1 = cases.(lcases-1) in
    if act0 = act1 then begin
      let low, high, inside, outside = coupe_inter 1 (lcases-2) cases in
      let _,(cmi,cinside) = opt_count false inside
      and _,(cmo,coutside) = opt_count false outside
      and cmij = {n=1 ; ni=(if low=high then 0 else 1)}
      and cij = {n=1 ; ni=(if low=high then 0 else 1)} in
      add_test cij cinside ;
      add_test cij coutside ;
      if less_tests cmi cmo then
        add_test cmij cmo
      else
        add_test cmij cmi ;
      Inter (1,lcases-2),(cmij,cij)
    end else
      Inter (-1,-1),(too_much, too_much) in
  if less2tests csep cinter then
    sep,csep
  else
    inter,cinter


  and enum top cases =
    let lcases = Array.length cases in
    let lim, with_sep =
      let best = ref (-1) and best_cost = ref (too_much,too_much) in

      for i = 1 to lcases-(1) do
        let lim,left,right = coupe cases i in
        let ci = {n=1 ; ni=0}
        and cm = {n=1 ; ni=0}
        and _,(cml,cleft) = opt_count false left
        and _,(cmr,cright) = opt_count false right in
        add_test ci cleft ;
        add_test ci cright ;
        if less_tests cml cmr then
          add_test cm cmr
        else
          add_test cm cml ;
        
        if
          less2tests (cm,ci) !best_cost
        then begin
          if top then
            Printf.fprintf stderr "Get it: %d\n" i ;
          best := i ;
          best_cost := (cm,ci)
        end
      done ;
      !best, !best_cost in
    let ilow, ihigh, with_inter =
      if lcases <= 2 then
        -1,-1,(too_much,too_much)
      else
        let rlow = ref (-1) and rhigh = ref (-1)
        and best_cost= ref (too_much,too_much) in
        for i=1 to lcases-2 do
          for j=i to lcases-2 do
            let low, high, inside, outside = coupe_inter i j cases in
            let _,(cmi,cinside) = opt_count false inside
            and _,(cmo,coutside) = opt_count false outside
            and cmij = {n=1 ; ni=(if low=high then 0 else 1)}
            and cij = {n=1 ; ni=(if low=high then 0 else 1)} in
            add_test cij cinside ;
            add_test cij coutside ;
            if less_tests cmi cmo then
              add_test cmij cmo
            else
              add_test cmij cmi ;
            if less2tests (cmij,cij) !best_cost then begin
              rlow := i ;
              rhigh := j ;
              best_cost := (cmij,cij)
            end
          done
        done ;
        !rlow, !rhigh, !best_cost in
    let r = ref (Inter (ilow,ihigh)) and rc = ref with_inter in
    if less2tests with_sep !rc then begin
      r := Sep lim ; rc := with_sep
    end ;
    !r, !rc

let make_if_test konst test arg i ifso ifnot =
  Arg.make_if
    (Arg.make_prim test [arg ; konst i])
    ifso ifnot

let make_if_lt konst arg i  ifso ifnot = match i with
| 1 ->
    make_if_test konst Arg.leint arg 0 ifso ifnot
| _ ->
    make_if_test konst Arg.ltint arg i ifso ifnot
    
and make_if_le konst arg i ifso ifnot = match i with
| -1 ->
    make_if_test konst Arg.ltint arg 0 ifso ifnot
| _ ->
    make_if_test konst Arg.leint arg i ifso ifnot

and make_if_gt konst arg i  ifso ifnot = match i with
| -1 ->
    make_if_test konst Arg.geint arg 0 ifso ifnot
| _ ->
    make_if_test konst Arg.gtint arg i ifso ifnot
    
and make_if_ge konst arg i  ifso ifnot = match i with
| 1 ->
    make_if_test konst Arg.gtint arg 0 ifso ifnot
| _ ->
    make_if_test konst Arg.geint arg i ifso ifnot

and make_if_eq  konst arg i ifso ifnot =
  make_if_test konst Arg.eqint arg i ifso ifnot

and make_if_ne  konst arg i ifso ifnot =
  make_if_test konst Arg.neint arg i ifso ifnot

let do_make_if_out h arg ifso ifno =
  Arg.make_if (Arg.make_isout h arg) ifso ifno
  
let make_if_out konst ctx l d mk_ifso mk_ifno = match l with
| 0 ->
    do_make_if_out
      (konst d) ctx.arg (mk_ifso ctx) (mk_ifno ctx)
| _ ->
    Arg.bind
      (Arg.make_offset ctx.arg (-l-ctx.off))
      (fun arg ->
        let ctx = {off= (-l) ; arg=arg} in
        do_make_if_out
          (konst d) arg (mk_ifso ctx) (mk_ifno ctx))

let do_make_if_in h arg ifso ifno =
  Arg.make_if (Arg.make_isin h arg) ifso ifno

let make_if_in konst ctx l d mk_ifso mk_ifno = match l with
| 0 ->
    do_make_if_in
      (konst d) ctx.arg (mk_ifso ctx) (mk_ifno ctx)
| _ ->
    Arg.bind
      (Arg.make_offset ctx.arg (-l-ctx.off))
      (fun arg ->
        let ctx = {off= (-l) ; arg=arg} in
        do_make_if_in
          (konst d) arg (mk_ifso ctx) (mk_ifno ctx))


let rec c_test konst ctx ({cases=cases ; actions=actions} as s) =
  let lcases = Array.length cases in
  assert(lcases > 0) ;
  if lcases = 1 then
    actions.(get_act cases 0) ctx
  else begin
    
    let w,c = opt_count false cases in
    match w with
    | No -> actions.(get_act cases 0) ctx
    | Inter (i,j) ->
        let low,high,inside, outside = coupe_inter i j cases in
        let _,(cinside,_) = opt_count false inside
        and _,(coutside,_) = opt_count false outside in
(* Costs are retrieved to put the code with more remaining tests
   in the privileged (positive) branch of ``if'' *)
        if low=high then begin
          if less_tests coutside cinside then
            make_if_eq
              konst ctx.arg
              (low+ctx.off)
              (c_test konst ctx {s with cases=inside})
              (c_test konst ctx {s with cases=outside})
          else
            make_if_ne
              konst ctx.arg
              (low+ctx.off)
              (c_test konst ctx {s with cases=outside})
              (c_test konst ctx {s with cases=inside})
        end else begin
          if less_tests coutside cinside then
            make_if_in
              konst ctx
              (low+ctx.off)
              (high-low)
              (fun ctx -> c_test konst ctx {s with cases=inside})
              (fun ctx -> c_test konst ctx {s with cases=outside})
          else
            make_if_out
              konst ctx
              (low+ctx.off)
              (high-low)
              (fun ctx -> c_test konst ctx {s with cases=outside})
              (fun ctx -> c_test konst ctx {s with cases=inside})
        end
    | Sep i ->
        let lim,left,right = coupe cases i in
        let _,(cleft,_) = opt_count false left
        and _,(cright,_) = opt_count false right in
        let left = {s with cases=left}
        and right = {s with cases=right} in

        if less_tests cright cleft then
          make_if_lt konst
            ctx.arg (lim+ctx.off)
            (c_test konst ctx left) (c_test konst ctx right)
        else
          make_if_ge konst
             ctx.arg (lim+ctx.off)
            (c_test konst ctx right) (c_test konst ctx left)
        
  end


(* Minimal density of switches *)
let theta = ref 0.33333

(* Minmal number of tests to make a switch *)
let switch_min = ref 3

(* Particular case 0, 1, 2 *)
let particular_case cases i j =
  j-i = 2 &&
  (let l1,h1,act1 = cases.(i)
  and  l2,h2,act2 = cases.(i+1)
  and  l3,h3,act3 = cases.(i+2) in
  l1+1=l2 && l2+1=l3 && l3=h3 &&
  act1 <> act3)

(* Sends back a boolean that says whether is switch is worth or not *)
let dense ({cases=cases ; actions=actions} as s) i j =
  if i=j then true
  else
    let l,_,_ = cases.(i)
    and _,h,_ = cases.(j) in
    let _,(_,{n=ntests}) =
      opt_count false (Array.sub cases i (j-i+1)) in
(*
  (ntests+1) >= theta * (h-l+1)
*)
    particular_case cases i j ||
    (ntests >= !switch_min &&
    float_of_int ntests +. 1.0 >=
    !theta *. (float_of_int h -. float_of_int l +. 1.0))

(* Compute clusters by dynamic programming
   Adaptation of the correction to Bernstein
   ``Correction to `Producing Good Code for the Case Statement' ''
   S.K. Kannan and T.A. Proebsting
   Software Practice and Exprience Vol. 24(2) 233 (Feb 1994)
*)
   

let comp_clusters ({cases=cases ; actions=actions} as s) =
  let len = Array.length cases in
  let min_clusters = Array.create len max_int
  and k = Array.create len 0 in
  let get_min i = if i < 0 then 0 else min_clusters.(i) in

  for i = 0 to len-1 do
    for j = 0 to i do
      if
        dense s j i &&
        get_min (j-1) + 1 < min_clusters.(i)
      then begin
        k.(i) <- j ;
        min_clusters.(i) <- get_min (j-1) + 1             
      end
    done
  done ;
  min_clusters.(len-1),k

(* Assume j > i *)
let make_switch  {cases=cases ; actions=actions} i j =
  let ll,_,_ = cases.(i)
  and _,hh,_ = cases.(j) in
  let tbl = Array.create (hh-ll+1) 0
  and t = Hashtbl.create 17
  and index = ref 0 in
  let get_index act =
    try
      Hashtbl.find t act
    with
    | Not_found ->
        let i = !index in
        incr index ;
        Hashtbl.add t act i ;
        i in

  for k=i to j do
    let l,h,act = cases.(k) in
    let index = get_index act in
    for kk=l-ll to h-ll do
      tbl.(kk) <- index
    done
  done ;
  let acts = Array.create !index actions.(0) in
  Hashtbl.iter
    (fun act i -> acts.(i) <- actions.(act))
    t ;
  (fun ctx ->
    match -ll-ctx.off with
    | 0 -> Arg.make_switch ctx.arg tbl acts
    | _ ->
        Arg.bind
          (Arg.make_offset ctx.arg (-ll-ctx.off))
          (fun arg -> Arg.make_switch arg tbl acts))


let make_clusters ({cases=cases ; actions=actions} as s) n_clusters k =
  let len = Array.length cases in
  let r = Array.create n_clusters (0,0,0)
  and t = Hashtbl.create 17
  and index = ref 0
  and bidon = ref (Array.length actions) in
  let get_index act =
    try
      let i,_ = Hashtbl.find t act in
      i
    with
    | Not_found ->
        let i = !index in
        incr index ;
        Hashtbl.add
          t act
          (i,(fun _ -> actions.(act))) ;
        i
  and add_index act =
    let i = !index in
    incr index ;
    incr bidon ;
    Hashtbl.add t !bidon (i,act) ;
    i in

  let rec zyva j ir =
    let i = k.(j) in
    begin if i=j then
      let l,h,act = cases.(i) in
      r.(ir) <- (l,h,get_index act)
    else (* assert i < j *)
      let l,_,_ = cases.(i)
      and _,h,_ = cases.(j) in
      r.(ir) <- (l,h,add_index (make_switch s i j))
    end ;
    if i > 0 then zyva (i-1) (ir-1) in
  
  zyva (len-1) (n_clusters-1) ;
  let acts = Array.create !index (fun _ -> assert false) in
  Hashtbl.iter (fun _ (i,act) -> acts.(i) <- act) t ;
  {cases = r ; actions = acts}
;;

  
let zyva konst arg cases actions = 
  let s = {cases=cases ; actions=actions} in
  let n_clusters,k = comp_clusters s in
  let clusters = make_clusters s n_clusters k in
  c_test konst {arg=arg ; off=0} clusters

and test_sequence konst arg cases actions =
  let s =
    {cases=cases ;
    actions=Array.map (fun act -> (fun _ -> act)) actions} in
   c_test konst {arg=arg ; off=0} s
;;

end
