open HolKernel boolLib bossLib BasicProvers dep_rewrite Parse
     arithmeticTheory dividesTheory listTheory rich_listTheory sortingTheory containerTheory relationTheory bagTheory;

val _ = new_theory "topdown_mergesortCorrectness";

(* START :: Top - down mergesort definitions *)
Definition TOP_DOWN_MERGEAUXILLARY_def:
  (top_down_mergeauxillary R xs [] = xs) /\
  (top_down_mergeauxillary R [] ys = ys) /\
  (top_down_mergeauxillary R (x::xs) (y::ys) =
    if R x y then x::(top_down_mergeauxillary R xs (y::ys))
    else y::(top_down_mergeauxillary R (x::xs) ys))
End

Definition TOP_DOWN_MERGESORT_def:
  (* we create the middle partition via the TAKE function *)
  (top_down_mergesort R [] = []) /\
  (top_down_mergesort R [x] = [x]) /\
  (top_down_mergesort R xs =
     top_down_mergeauxillary R (top_down_mergesort R (TAKE ((LENGTH xs) DIV 2) xs)) (top_down_mergesort R (DROP ((LENGTH xs) DIV 2) xs)))
Termination
  WF_REL_TAC `measure (LENGTH o SND)` >>
  rw[]
  >- (
      rw[] >>
      match_mp_tac DIV_POS >>
      decide_tac
    )
  >- (
      simp[LENGTH_TAKE_EQ] >>
      Cases_on `SUC (SUC (LENGTH v7)) DIV 2 <= SUC (SUC (LENGTH v7))`
      >- (rw[])
      >- (
          rw[] >>
          (* Here we show that given our assumptions, this is not possible. i.e. prove F *)
          qspecl_then [`SUC (SUC (LENGTH v7))`, `2`] assume_tac DIV_LESS >>
          gvs[]
        )
    )
End
(* END :: Top - down mergesort definitions *)

(* START :: Top - down mergesort correctness theorems *)
Theorem MEM_TOP_DOWN_MERGEAUXILLARY_lemma:
  !R xs ys. (MEM x (top_down_mergeauxillary R xs ys)) = ((MEM x xs) \/ (MEM x ys))
Proof
  ho_match_mp_tac TOP_DOWN_MERGEAUXILLARY_ind >>
  rw[TOP_DOWN_MERGEAUXILLARY_def] >>
  metis_tac[]
QED

Theorem SORTED_MERGEAUXILLARY_lemma:
  !R xs ys. (transitive R /\ total R) ==> (SORTED R (top_down_mergeauxillary R xs ys) <=> (SORTED R xs) /\ (SORTED R ys))
Proof
  ho_match_mp_tac TOP_DOWN_MERGEAUXILLARY_ind >>
  rpt strip_tac
  >- (rw[TOP_DOWN_MERGEAUXILLARY_def])
  >- (rw[TOP_DOWN_MERGEAUXILLARY_def])
  >- (
      rw[TOP_DOWN_MERGEAUXILLARY_def]
      >- (
          fs[SORTED_EQ] >>
          rw[EQ_IMP_THM]
          >- (simp[MEM_TOP_DOWN_MERGEAUXILLARY_lemma])
          >- (
              fs[MEM_TOP_DOWN_MERGEAUXILLARY_lemma] >>
              metis_tac[total_def, transitive_def]
            )
        )
      >- (
          fs[SORTED_EQ] >>
          rw[EQ_IMP_THM]
          >- (
              simp[MEM_TOP_DOWN_MERGEAUXILLARY_lemma]
            )
          >- (
              fs[MEM_TOP_DOWN_MERGEAUXILLARY_lemma]
              >- (metis_tac[total_def, transitive_def])
              >- (metis_tac[total_def, transitive_def])
            )
        )
    )
QED

Theorem CORRECTNESS_SORTED_TOP_DOWN_MERGESORT_thm:
  !R xs. (total R /\ transitive R) ==> SORTED R (top_down_mergesort R xs)
Proof
  ho_match_mp_tac TOP_DOWN_MERGESORT_ind >>
  rpt strip_tac
  >- (rw[TOP_DOWN_MERGESORT_def])
  >- (rw[TOP_DOWN_MERGESORT_def])
  >- (
      rw[TOP_DOWN_MERGESORT_def, TOP_DOWN_MERGEAUXILLARY_def] >>
      simp[SORTED_MERGEAUXILLARY_lemma] >>
      gvs[]
    )
QED

Theorem MSET_MERGEAUXILLARY_lemma:
  !R xs ys. LIST_TO_BAG (top_down_mergeauxillary R xs ys) 
    = BAG_UNION ( LIST_TO_BAG xs ) (LIST_TO_BAG ys)
Proof
  (* {| mergeauxillary R xs ys |} = {| xs |} UNION {| ys |} *)
  ho_match_mp_tac TOP_DOWN_MERGEAUXILLARY_ind >>
  rpt strip_tac
  >- (
      rw[LIST_TO_BAG_def] >>
      `top_down_mergeauxillary R xs [] = xs` by metis_tac[TOP_DOWN_MERGEAUXILLARY_def] >>
      fs[]
    )
  >- (
      rw[LIST_TO_BAG_def] >>
      simp[BAG_UNION_EMPTY] >>
      `top_down_mergeauxillary R xs [] = xs` by metis_tac[TOP_DOWN_MERGEAUXILLARY_def] >>
      fs[TOP_DOWN_MERGEAUXILLARY_def]
    )
  >- (
      rw[TOP_DOWN_MERGEAUXILLARY_def, LIST_TO_BAG_def]
      >- (metis_tac[BAG_UNION_INSERT])
      >- (
          metis_tac[BAG_UNION_INSERT, ASSOC_BAG_UNION, COMM_BAG_UNION]
        )
    )
QED

Theorem CORRECTNESS_MSET_TOP_DOWN_MERGESORT_thm:
  !R xs. LIST_TO_BAG (top_down_mergesort R xs) = LIST_TO_BAG xs
Proof
  (* We want to show: {| top_down_mergesort R xs |} = {| xs |} *)
  ho_match_mp_tac TOP_DOWN_MERGESORT_ind >>
  rpt strip_tac
  >- (rw[TOP_DOWN_MERGESORT_def])
  >- (rw[TOP_DOWN_MERGESORT_def])
  >- (
      rw[TOP_DOWN_MERGESORT_def, TOP_DOWN_MERGEAUXILLARY_def] >>
      gvs[MSET_MERGEAUXILLARY_lemma] >>
      simp[GSYM LIST_TO_BAG_APPEND]
    )
QED

(* END :: Top - down mergesort correctness theorems *)

val _ = export_theory ()
