(* ========================================================================= *)
(* namespace: port of HOL4 semantics/namespaceScript.sml (CakeML v3479).     *)
(* Defines a datatype for nested namespaces where names can be either        *)
(* short (e.g. foo) or long (e.g. ModuleA.InnerB.bar).                       *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

(* HOL4: Type alist = ``: ('k # 'v) list``  (written out where used) *)

(* Identifiers *)

let id_INDUCT,id_RECURSION = cake_type "id = Short N | Long M id";;

let mk_id_def = cake_def
  `(mk_id [] (n:N) = Short n:(M,N)id) /\
   (mk_id (CONS (mn:M) mns) n = Long mn (mk_id mns n))`;;

let id_to_n_def = cake_def
  `(id_to_n (Short (n:N):(M,N)id) = n) /\
   (id_to_n (Long (m:M) id) = id_to_n id)`;;

let id_to_mods_def = cake_def
  `(id_to_mods (Short (n:N):(M,N)id) = []:M list) /\
   (id_to_mods (Long mn id) = CONS mn (id_to_mods id))`;;

let namespace_INDUCT,namespace_RECURSION =
  cake_type "namespace = Bind ((N#V) list) ((M#namespace) list)";;

let nsLookup_def = cake_def_wf
  `MEASURE (\p:(M,N,V)namespace#(M,N)id. id_size (\x:M. 0) (\x:N. 0) (SND p))`
  (REWRITE_TAC[measure_THM; FST; SND; type_size_def "id"] THEN ARITH_TAC)
  `(nsLookup (Bind v m:(M,N,V)namespace) (Short n) = ALOOKUP v n) /\
   (nsLookup (Bind v m) (Long mn id) =
      match ALOOKUP m mn with
        NONE -> NONE
      | SOME env -> nsLookup env id)`;;

let nsLookup_ind = cake_ind "nsLookup";;

let nsLookupMod_def = cake_def_wf
  `MEASURE (\p:(M,N,V)namespace#M list. LENGTH (SND p))`
  (REWRITE_TAC[measure_THM; FST; SND; LENGTH] THEN ARITH_TAC)
  `(nsLookupMod (e:(M,N,V)namespace) [] = SOME e) /\
   (nsLookupMod (Bind v m) (CONS mn path) =
      match ALOOKUP m mn with
        NONE -> NONE
      | SOME env -> nsLookupMod env path)`;;

let nsLookupMod_ind = cake_ind "nsLookupMod";;

let nsEmpty_def = cake_def
  `nsEmpty:(M,N,V)namespace = Bind [] []`;;

let nsAppend_def = cake_def
  `nsAppend (Bind v1 m1:(M,N,V)namespace) (Bind v2 m2) =
     Bind (APPEND v1 v2) (APPEND m1 m2)`;;

let nsLift_def = cake_def
  `nsLift (mn:M) (env:(M,N,V)namespace) = Bind [] [(mn,env)]`;;

let alist_to_ns_def = cake_def
  `alist_to_ns (a:(N#V) list) = Bind a []:(M,N,V)namespace`;;

let nsBind_def = cake_def
  `nsBind (k:N) (x:V) (Bind v m:(M,N,V)namespace) = Bind (CONS (k,x) v) m`;;

let nsBindList_def = cake_def
  `nsBindList (l:(N#V) list) (e:(M,N,V)namespace) =
     ITLIST (\xv e. match xv with (x,v) -> nsBind x v e) l e`;;

let nsOptBind_def = cake_def
  `nsOptBind (n:N option) (x:V) (env:(M,N,V)namespace) =
     match n with NONE -> env | SOME n -> nsBind n x env`;;

let nsSing_def = cake_def
  `nsSing (n:N) (x:V) = Bind [(n,x)] []:(M,N,V)namespace`;;

let nsSub_def = cake_def
  `nsSub (r:(M,N)id->V1->V2->bool) (env1:(M,N,V1)namespace)
         (env2:(M,N,V2)namespace) <=>
     (!id v1.
        nsLookup env1 id = SOME v1 ==>
        ?v2. nsLookup env2 id = SOME v2 /\ r id v1 v2) /\
     !path. nsLookupMod env2 path = NONE ==> nsLookupMod env1 path = NONE`;;

let nsAll_def = cake_def
  `nsAll (f:(M,N)id->V->bool) (env:(M,N,V)namespace) <=>
     !id v. nsLookup env id = SOME v ==> f id v`;;

let nsAll2_def = cake_def
  `nsAll2 (r:(M,N)id->V1->V2->bool) (env1:(M,N,V1)namespace)
          (env2:(M,N,V2)namespace) <=>
     nsSub r env1 env2 /\ nsSub (\x y z. r x z y) env2 env1`;;

let nsDom_def = cake_def
  `nsDom (env:(M,N,V)namespace) = {n | ?v. nsLookup env n = SOME v}`;;

let nsDomMod_def = cake_def
  `nsDomMod (env:(M,N,V)namespace) = {n | ?v. nsLookupMod env n = SOME v}`;;


let nsMap_def = cake_def_wf
  `MEASURE (\p:(V->W)#(M,N,V)namespace.
              namespace_size (\x:M. 0) (\x:N. 0) (\x:V. 0) (SND p))`
  TERM_TAC
  `nsMap (f:V->W) (Bind v m:(M,N,V)namespace) =
     Bind (MAP (\nx. match nx with (n,x) -> (n,f x)) v)
          (MAP (\me. match me with (mn,e) -> (mn,nsMap f e)) m)`;;

let nsMap_ind = cake_ind "nsMap";;
