(* ========================================================================= *)
(* HashtableProg: port of HOL4 basis/HashtableProgScript.sml (CakeML        *)
(* v3479).  A module about hash tables for the CakeML standard basis        *)
(* library.  The CakeML text of the Quote add_cakeml blocks is HOL4's,       *)
(* verbatim, at HOL4's source positions (add_cakeml_at).  HOL4's EVAL of    *)
(* the constructor lookup is ml_progLib's lookup                              *)
(* conversion.                                                               *)
(*                                                                           *)
(* Local structure (HOL4 comment):                                           *)
(*   local hashtable (hidden) in delete, lookup, toAscList, size,            *)
(*   local initBuckets (hidden) in empty, clear,                             *)
(*   local staticInsert (hidden) in local doubleCapacity (hidden) in         *)
(*   insert.                                                                 *)
(* ========================================================================= *)

needs "basis/SetProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "SetProg";;

ml_prog_update (ml_prog_open_module "Hashtable");;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (45,18) {|
  datatype ('k, 'v) hashtable =
  Hashtable
    (int ref) (*Element counter*)
    ((('k,'v) Map.map) array ref) (*Buckets*)
    ('k -> int) (*Hash function*)
    ('k -> 'k -> ordering) (*Key compare function*)
|};;

let hashtable_ty_env = ml_prog_get_env (get_ml_prog_state ());;
let stamp_eval = ml_prog_lookup_eq_conv
  (vsubst [hashtable_ty_env, `e:v sem_env`]
     `nsLookup (sem_env_c (e:v sem_env)) (Short (implode "Hashtable"))`);;
let hashtable_con_stamp = rhs (concl stamp_eval);;

let hashtable_con_stamp_def = new_definition
  (mk_eq (`hashtable_con_stamp:stamp option`,
          mk_comb (`OPTION_MAP (SND:num#stamp->stamp)`, hashtable_con_stamp)));;

ml_prog_update ml_prog_open_local_in_block;;

(* provides the Hashtable.hashtable name for the hashtable type *)
ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"; implode "'b"] (implode "hashtable")
     (Atapp [Atvar (implode "'a"); Atvar (implode "'b")] (Short (implode "hashtable")))` I);;

add_cakeml_at (68,18) {|
  fun delete ht k =
    case ht of Hashtable usedRef bucketsRef hf _ =>
      let
        val buckets = !bucketsRef
        val index = (hf k) mod (Array.length buckets)
        val bucket = Array.sub buckets index
        val newBucket = Map.delete bucket k
      in
        Array.update buckets index newBucket;
        if not (Map.null bucket) andalso Map.null newBucket
              andalso (0 < (!usedRef)) then (
          usedRef := (!usedRef)-1 )
        else
          ()
      end
|};;

add_cakeml_at (86,18) {|
  fun lookup ht k =
    case ht of Hashtable usedRef bucketsRef hf cmp =>
      let
        val buckets = !bucketsRef
        val bucket = Array.sub buckets ((hf k) mod (Array.length buckets))
      in
        Map.lookup bucket k
    end
|};;

add_cakeml_at (97,18) {|
  fun toAscList ht =
    case ht of Hashtable _ bucketsRef _ cmp =>
      Map.toAscList (Array.foldr Map.union (Map.empty cmp) (!bucketsRef))
|};;

add_cakeml_at (103,18) {|
  fun size ht =
    case ht of Hashtable usedRef bucketsRef hf cmp =>
      !usedRef
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (111,18) {|
  fun initBuckets n cmp = Array.array n (Map.empty cmp)
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (117,18) {|
  fun empty size hf cmp =
    ( Hashtable
      (Ref 0)
      (Ref (initBuckets (if size < 1 then 1 else size) cmp))
      hf
      cmp
    )
|};;

add_cakeml_at (127,18) {|
  fun clear ht =
    case ht of Hashtable usedRef bucketsRef _ cmp =>
      (bucketsRef := initBuckets (Array.length (!bucketsRef)) cmp;
      usedRef := (!usedRef)*0)
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (136,18) {|
  fun staticInsert ht k v =
    case ht of Hashtable usedRef bucketsRef hf cmp =>
      let
        val buckets = !bucketsRef
        val index = (hf k) mod (Array.length buckets)
        val bucket = Array.sub buckets index
      in
        Array.update buckets index (Map.insert bucket k v);
        if Map.null bucket then (
          usedRef := (!usedRef)+1 )
        else
          ()
      end
|};;

ml_prog_update ml_prog_open_local_in_block;;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (155,18) {|
  fun insertList ht l = List.app (fn (k,v) => staticInsert ht k v) l
|};;

add_cakeml_at (159,18) {|
  fun doubleCapacity ht =
    case ht of Hashtable usedRef bucketsRef _ cmp =>
      let
        val oldArr = !bucketsRef
        val newLen = Array.length oldArr * 2
        val oldList = toAscList ht
      in
        usedRef := 0;
        bucketsRef := initBuckets newLen cmp;
        insertList ht oldList
      end
|};;

ml_prog_update ml_prog_open_local_in_block;;

(* Load treshold values for insert function, default 3/4 (HOL4 comment) *)

add_cakeml_at (176,18) {|
  fun insert ht k v =
    case ht of Hashtable usedRef bucketsRef _ _ =>
      if (4*(!usedRef))<(3* (Array.length (!bucketsRef)))
      then staticInsert ht k v
      else (doubleCapacity ht; staticInsert ht k v)
|};;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
