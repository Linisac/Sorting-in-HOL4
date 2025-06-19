open HolKernel boolLib bossLib BasicProvers dep_rewrite Parse
     listTheory sortingTheory relationTheory containerTheory bagTheory;

val _ = new_theory "bottomup_mergesortCorrectness";

(* START :: Bottom - up mergesort definitions *)
Definition BOTTOM_UP_MERGEAUXILLARY_def:
  (* bottom_up_mergeauxillary :: ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list *)
  (bottom_up_mergeauxillary R xs [] = xs) /\
  (bottom_up_mergeauxillary R [] ys = ys) /\
  (bottom_up_mergeauxillary R (x::xs) (y::ys) =
    if R x y then x::(bottom_up_mergeauxillary R xs (y::ys))
    else y::(bottom_up_mergeauxillary R (x::xs) ys))
End

Definition BOTTOM_UP_MERGEADJACENT_def:
  (* bottom_up_mergeadjacent :: ('a -> 'a -> Bool) -> 'a List List -> 'a List List *)
  (bottom_up_mergeadjacent R [] = []) /\
  (bottom_up_mergeadjacent R [xs] = [xs]) /\
  (bottom_up_mergeadjacent R (xs::ys::lst) = 
    (bottom_up_mergeauxillary R xs ys) :: 
    (bottom_up_mergeadjacent R lst))
End

Definition BOTTOM_UP_MERGEALL_def:
  (* bottom_up_mergeall :: ('a -> 'a -> Bool) -> 'a List List -> 'a List *)
  (bottom_up_mergeall R [] = []) /\
  (bottom_up_mergeall R [xs] = xs) /\
  (bottom_up_mergeall R xss = bottom_up_mergeall R (bottom_up_mergeadjacent R xss)) 
Termination
  WF_REL_TAC `measure (LENGTH o SND)` >>
  Induct_on `v7`
  >- (rw[BOTTOM_UP_MERGEADJACENT_def])
  >- (
      `! R l. LENGTH (bottom_up_mergeadjacent R l) < SUC (LENGTH l)` by (
        ho_match_mp_tac BOTTOM_UP_MERGEADJACENT_ind >>
        rw[BOTTOM_UP_MERGEADJACENT_def]
      ) >>
      rw[BOTTOM_UP_MERGEADJACENT_def, BOTTOM_UP_MERGEAUXILLARY_def] >>
      pop_assum (fn x => qspecl_then [`R`, `h::v7`] assume_tac x) >>
      gvs[]
    )
End

Definition BOTTOM_UP_MERGESORT_def:
  (* bottom_up_mergesort R xs = ('a -> 'a -> bool) -> 'a List -> 'a List *)
  bottom_up_mergesort R xs = bottom_up_mergeall R (MAP (\x. [x]) xs)
End
(* END :: Bottom - up mergesort definitions *)

(* START :: Bottom - up mergesort correctness sortedness theorems *)
Theorem MEM_BOTTOM_UP_MERGEAUXILLARY_lemma:
  !R xs ys. (MEM x (bottom_up_mergeauxillary R xs ys)) = ((MEM x xs) \/ (MEM x ys))
Proof
  ho_match_mp_tac BOTTOM_UP_MERGEAUXILLARY_ind >>
  rw[BOTTOM_UP_MERGEAUXILLARY_def] >>
  metis_tac[]
QED

Theorem SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma:
  !R xs ys. (transitive R /\ total R) ==> (SORTED R (bottom_up_mergeauxillary R xs ys) <=> (SORTED R xs) /\ (SORTED R ys))
Proof
  ho_match_mp_tac BOTTOM_UP_MERGEAUXILLARY_ind >>
  rpt strip_tac
  >- (rw[BOTTOM_UP_MERGEAUXILLARY_def])
  >- (rw[BOTTOM_UP_MERGEAUXILLARY_def])
  >- (
      rw[BOTTOM_UP_MERGEAUXILLARY_def]
      >- (
          fs[SORTED_EQ] >>
          rw[EQ_IMP_THM]
          >- (simp[MEM_BOTTOM_UP_MERGEAUXILLARY_lemma])
          >- (
              fs[MEM_BOTTOM_UP_MERGEAUXILLARY_lemma] >>
              metis_tac[total_def, transitive_def]
            )
        )
      >- (
          fs[SORTED_EQ] >>
          rw[EQ_IMP_THM]
          >- (
              simp[MEM_BOTTOM_UP_MERGEAUXILLARY_lemma]
            )
          >- (
              fs[MEM_BOTTOM_UP_MERGEAUXILLARY_lemma]
              >- (metis_tac[total_def, transitive_def])
              >- (metis_tac[total_def, transitive_def])
            )
        )
    )
QED

Theorem SORTED_BOTTOM_UP_MERGEADJACENT_lemma:
  !R xss. (transitive R /\ total R) ==> ((EVERY (SORTED R) (bottom_up_mergeadjacent R xss)) <=> EVERY (SORTED R) xss)
Proof
  ho_match_mp_tac BOTTOM_UP_MERGEADJACENT_ind >>
  rpt strip_tac
  >- (simp[BOTTOM_UP_MERGEADJACENT_def])
  >- (simp[BOTTOM_UP_MERGEADJACENT_def])
  >- (
      fs[BOTTOM_UP_MERGEADJACENT_def, SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma] >>
      metis_tac[]
    )
QED

Theorem BOTTOM_UP_MERGEALL_MAP_lemma:
  !R xss. (transitive R /\ total R) ==> ( SORTED R (bottom_up_mergeall R xss) <=> (EVERY (SORTED R) xss) )
Proof
  ho_match_mp_tac BOTTOM_UP_MERGEALL_ind >>
  rpt strip_tac
  >- (simp[BOTTOM_UP_MERGEALL_def])
  >- (simp[BOTTOM_UP_MERGEALL_def])
  >- (
      fs[BOTTOM_UP_MERGEALL_def, BOTTOM_UP_MERGEADJACENT_def, SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma, SORTED_BOTTOM_UP_MERGEADJACENT_lemma] >>
      metis_tac[]
    )
QED

Theorem CORRECTNESS_SORTED_BOTTOM_UP_MERGESORT_thm:
  !R xs. (total R /\ transitive R) ==> SORTED R (bottom_up_mergesort R xs)
Proof
  rw[BOTTOM_UP_MERGESORT_def, BOTTOM_UP_MERGEALL_MAP_lemma, EVERY_MAP]
QED
(* END :: Bottom - up mergesort correctness sortedness theorems *)

(* START :: Bottom - up mergesort correctness mset theorems *)
Theorem MSET_BOTTOM_UP_MERGEAUXILLARY_lemma:
  !R l1 l2. LIST_TO_BAG (bottom_up_mergeauxillary R l1 l2) = BAG_UNION (LIST_TO_BAG l1) (LIST_TO_BAG l2)
Proof
  ho_match_mp_tac BOTTOM_UP_MERGEAUXILLARY_ind >>
  rpt strip_tac
  >- (simp[BOTTOM_UP_MERGEAUXILLARY_def])
  >- (simp[BOTTOM_UP_MERGEAUXILLARY_def])
  >- (
      fs[BOTTOM_UP_MERGEAUXILLARY_def] >>
      rw[]
      >- (simp[BAG_UNION_INSERT])
      >- (
          simp[BAG_UNION_INSERT] >>
          metis_tac[ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]
        )
    )
QED

Theorem MSET_BOTTOM_UP_MERGEADJACENT_lemma:
  !R xss. LIST_TO_BAG ( FLAT (bottom_up_mergeadjacent R xss)) = LIST_TO_BAG (FLAT xss)
Proof
  (* 
    Recall that mergeadjacent will return ('a List List) and xss is ('a List List).
    It will simplify things if we can flatten the lists
    FLAT is very handy here.
  *)
  ho_match_mp_tac BOTTOM_UP_MERGEADJACENT_ind >>
  rpt strip_tac
  >- (simp[BOTTOM_UP_MERGEADJACENT_def])
  >- (simp[BOTTOM_UP_MERGEADJACENT_def])
  >- (
      simp[BOTTOM_UP_MERGEADJACENT_def] >>
      metis_tac[LIST_TO_BAG_APPEND,MSET_BOTTOM_UP_MERGEAUXILLARY_lemma]
    )
QED

Theorem MSET_BOTTOM_UP_MERGEALL_lemma:
  !R xss. LIST_TO_BAG (bottom_up_mergeall R xss) = LIST_TO_BAG (FLAT xss)
Proof
  (* 
    Recall that mergeall will return ('a List) but xss is ('a List List).
  *)
  ho_match_mp_tac BOTTOM_UP_MERGEALL_ind >>
  rpt strip_tac
  >- (simp[BOTTOM_UP_MERGEALL_def])
  >- (simp[BOTTOM_UP_MERGEALL_def])
  >- (
      fs[BOTTOM_UP_MERGEALL_def, BOTTOM_UP_MERGEADJACENT_def, LIST_TO_BAG_APPEND] >>
      simp[MSET_BOTTOM_UP_MERGEAUXILLARY_lemma, MSET_BOTTOM_UP_MERGEADJACENT_lemma]
    )
QED

Theorem CORRECTNESS_MSET_BOTTOM_UP_MERGESORT_thm:
  !R xs. LIST_TO_BAG (bottom_up_mergesort R xs) = LIST_TO_BAG xs
Proof
  simp[BOTTOM_UP_MERGESORT_def, BOTTOM_UP_MERGEALL_def, MSET_BOTTOM_UP_MERGEALL_lemma] >>
  Induct_on `xs` >> simp[]
QED
(* END :: Bottom - up mergesort correctness mset theorems *)

val _ = export_theory ()
