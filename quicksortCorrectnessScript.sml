open HolKernel boolLib bossLib BasicProvers dep_rewrite Parse
     arithmeticTheory listTheory rich_listTheory sortingTheory
     relationTheory containerTheory bagTheory pred_setTheory;

val _ = new_theory "quicksortCorrectness"

Definition QUICKSORT_def[simp]:
  (quicksort R [] = []) /\
  (quicksort R (x::xs) =
    (quicksort R (FILTER (\y. R y x) xs)) ++ [x] ++ (quicksort R (FILTER (\y. ~R y x) xs)))
Termination
  WF_REL_TAC `measure (LENGTH o SND)` >>
  rw[LENGTH]
  >- (
      qspecl_then [`(\y. ~R y x)`, `xs`] assume_tac LENGTH_FILTER_LEQ >>
      fs[LESS_EQ_IMP_LESS_SUC]
    )
  >- (
      qspecl_then [`(\y. R y x)`, `xs`] assume_tac LENGTH_FILTER_LEQ >>
      fs[LESS_EQ_IMP_LESS_SUC]
    )
End

(* START :: Quicksort correctness theorems *)
Theorem MEM_QUICKSORT_lemma:
  !R xs. MEM x (quicksort R xs) = MEM x xs
Proof
  ho_match_mp_tac QUICKSORT_ind >>
  rpt strip_tac
  >- (rw[])
  >- (
      rw[MEM_FILTER] >>
      metis_tac[]
    )
QED 

Theorem CORRECTNESS_SORTED_QUICKSORT_thm:
  !R xs. (total R /\ transitive R) ==> SORTED R (quicksort R xs)
Proof
  ho_match_mp_tac QUICKSORT_ind >>
  rpt strip_tac
  >- (
      rw[]
    )
  >- (
      rw[] >>
      fs[SORTED_APPEND] >>
      simp[MEM_QUICKSORT_lemma, MEM_FILTER] >>
      rpt strip_tac
      >- (metis_tac[total_def, transitive_def])
      >- (metis_tac[total_def, transitive_def])
    )
QED

Theorem CORRECTNESS_MSET_QUICKSORT_thm:
  !R xs. LIST_TO_BAG (quicksort R xs) = LIST_TO_BAG xs
Proof
  ho_match_mp_tac QUICKSORT_ind >>
  rpt strip_tac
  >- (rw[])
  >- (
      rw[LIST_TO_BAG_def, LIST_TO_BAG_APPEND] >>
      (* will shift terms with assoc and comm properties of BAG_UNION via magic. *)
      simp [AC ASSOC_BAG_UNION COMM_BAG_UNION] >> 
      rw[LIST_TO_BAG_FILTER] >>
      `(\y. ~R y x) = COMPL (\y. R y x)` by SET_TAC[COMPL_DEF, DIFF_DEF] >>
      rw[BAG_FILTER_SPLIT, BAG_INSERT_UNION]
    )
QED

(* END :: Quicksort correctness theorems *)

val _ = export_theory();
