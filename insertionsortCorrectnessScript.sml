open HolKernel boolLib bossLib BasicProvers dep_rewrite Parse
     pred_setTheory listTheory rich_listTheory bagTheory sortingTheory relationTheory containerTheory;

val _ = new_theory "insertionsortCorrectness";

(* START :: insertion sort definitions *)
Definition INSERTION_AUXILLARY_def:
  (insertionAuxillary R x [] = [x]) /\
  (insertionAuxillary R x (y::ys) =
    if R x y then x::y::ys
    else y :: (insertionAuxillary R x ys))
End

Definition INSERTIONSORT_def:
  insertionsort R [] = [] /\
  insertionsort R (x::xs) = insertionAuxillary R x (insertionsort R xs)
End
(* END :: insertion sort definitions *)

(* START :: Insertion aux && sort membership arguments *)
Theorem MEM_INSERTIONAUXILLARY_lemma:
  MEM e (insertionAuxillary R x xs) <=> (MEM e [x]) \/ (MEM e xs)
Proof
  Induct_on `xs`
  >- (
      fs[INSERTION_AUXILLARY_def]
    )
  >- (
      rw[INSERTION_AUXILLARY_def, MEM] >>
      (* not sure why DISJ_COMM didn't work for me *)
      SET_TAC[]
    )
QED
(* END :: Insertion aux && sort membership arguments *)

(* START :: insertion sort SORTED theorems *)
Theorem SORTED_INSERTIONAUXILLARY_lemma:
  (total R /\ transitive R) ==> (SORTED R (insertionAuxillary R x xs) <=> SORTED R xs)
Proof
  strip_tac >>
  Induct_on `xs`
  >- (
      rw[INSERTION_AUXILLARY_def]
    )
  >- (
    rw[INSERTION_AUXILLARY_def, SORTED_EQ] >>
    `(SORTED R xs) ==> ((!y. MEM y (insertionAuxillary R x xs) ==> R h y) <=> !y. MEM y xs ==> R h y)` suffices_by metis_tac[] >>
    strip_tac >>
    simp[MEM_INSERTIONAUXILLARY_lemma] >>
    iff_tac
    >- (
        strip_tac >>
        rw[MEM_INSERTIONAUXILLARY_lemma]
      )
    >- (
        strip_tac >>
        (* not sure why the rw[DISJ_IMP_THM, FORALL_AND_THM] works wonders...*)
        rw[DISJ_IMP_THM, FORALL_AND_THM] >>
        metis_tac[total_def]
      )
    )
QED

Theorem CORRECTNESS_SORTED_INSERTIONSORT_thm:
  (total R /\ transitive R) ==> SORTED R (insertionsort R xs)
Proof
  rw[] >>
  Induct_on `xs`
  >- (
      rw[INSERTIONSORT_def, SORTED_DEF]
    )
  >- (
      simp[INSERTIONSORT_def, SORTED_INSERTIONAUXILLARY_lemma]
    )
QED
(* END :: insertion sort SORTED theorems *)

(* START :: insertion sort multiset theorems *)
Theorem MSET_INSERTION_AUXILLARY_lemma:
  LIST_TO_BAG (insertionAuxillary R x xs) = LIST_TO_BAG (x::xs)
Proof
  Induct_on `xs`
  >- (
      rw[INSERTION_AUXILLARY_def]
    )
  >- (
      rw[INSERTION_AUXILLARY_def] >>
      metis_tac [BAG_INSERT_commutes]
    )
QED

Theorem CORRECTNNESS_MSET_INSERTSORT:
  LIST_TO_BAG (insertionsort R xs) = LIST_TO_BAG xs
Proof
  Induct_on `xs`
  >- (
      rw[INSERTIONSORT_def]
    )
  >- (
      rw[INSERTIONSORT_def, LIST_TO_BAG_def, MSET_INSERTION_AUXILLARY_lemma]
    )
QED
(* END :: insertion sort multiset theorems *)

val _ = export_theory()
