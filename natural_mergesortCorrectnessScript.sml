open HolKernel boolLib bossLib BasicProvers dep_rewrite Parse
     listTheory rich_listTheory sortingTheory relationTheory containerTheory bagTheory;

val _ = new_theory "natural_mergesortCorrectness"

(* START :: Natural mergesort definitions *)
Definition NATURAL_MERGEAUXILLARY_def:
  (natural_mergeauxillary R [] ys = ys) /\
  (natural_mergeauxillary R xs []  = xs) /\
  (natural_mergeauxillary R (x::xs) (y::ys) = 
    if R x y then x::(natural_mergeauxillary R xs (y::ys))
    else y::(natural_mergeauxillary R (x::xs) ys))
End

Definition NATURAL_MERGEADJACENT_def:
  (* natural_mergeadjacent :: 'a List List -> 'a List List *)
  (natural_mergeadjacent R [] = []) /\
  (natural_mergeadjacent R [xs] = [xs]) /\
  (natural_mergeadjacent R (x::y::zs) = 
    (natural_mergeauxillary R x y) :: (natural_mergeadjacent R zs))
End

Definition NATURAL_MERGEALL_def:
  (* natural_mergeall :: 'a List List -> 'a List *)
  (natural_mergeall R [] = []) /\
  (natural_mergeall R [xs] = xs) /\
  (natural_mergeall R xss = natural_mergeall R (natural_mergeadjacent R xss))
Termination
  WF_REL_TAC `measure (LENGTH o SND)` >>
  simp[NATURAL_MERGEADJACENT_def] >>
  Induct_on `v7`
  >- (simp[NATURAL_MERGEADJACENT_def])
  >- (
      rw[NATURAL_MERGEADJACENT_def] >>
      Cases_on `v7`
      >- (simp[NATURAL_MERGEADJACENT_def])
      >- (
          fs[NATURAL_MERGEADJACENT_def, LENGTH] >>
          `!R t. LENGTH (natural_mergeadjacent R t) < SUC (LENGTH t)` by (
            ho_match_mp_tac NATURAL_MERGEADJACENT_ind >>
            rpt strip_tac >> simp[NATURAL_MERGEADJACENT_def]
          ) >>
          pop_assum (fn x => qspecl_then [`R`, `t`] assume_tac x) >>
          gvs[]
        )
    )
End

Definition NATURAL_MERGE_ASC_RUNS_DESC_def:
  (*
    runs will partition a list into sublists of ascending and descending sequences.
    We do this so that we get the best case when we pass it into natural_mergeall

    Performance issues from (++) in asc.
    See the equivalence theorem with the efficient version below.
  *)

  (* asc :: ('a -> 'a -> bool) -> 'a -> 'a List -> 'a List -> 'a List List *)
  (asc R a as (b::bs) =
    if R a b then asc R b (as ++ [a]) bs
    else (as ++ [a]) :: (runs R (b::bs))) /\
  (asc R a as [] = [as ++ [a]])
  /\
  (* runs :: ('a -> 'a -> bool) -> 'a List -> 'a List List *)
  (runs R (a::b::xs) =
    if ~(R a b) then desc R b [a] xs
    else asc R b [a] xs) /\
  (runs R [x] = [[x]]) /\
  (runs R [] = [])
  /\
  (* desc :: ('a -> 'a -> bool) -> 'a -> 'a List -> 'a List -> 'a List List *)
  (desc R a as (b::bs) =
    if ~(R a b) then desc R b (a::as) bs
    else (a::as) :: runs R (b::bs)) /\
  (desc R a as [] = [a::as]) 
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (R, b, as, xs) => LENGTH xs + 1
    | INR (INR (R, b, as, xs)) => LENGTH xs + 1
    | INR (INL (R,bs)) => LENGTH bs
  )` >> 
  rw[]
End

Definition NATURAL_MERGE_ASC_RUNS_DESC'_def:
  (* asc' :: ('a -> 'a -> bool) -> 'a -> ('a List -> 'a List) -> 'a List -> 'a List List *)
  (asc' R a as (b::bs) =
    if R a b then asc' R b (as o CONS a) bs
    else as [a] :: (runs' R (b::bs)) ) /\
  (asc' R a as [] = [ (as [a]) ])
  /\
  (* runs' :: ('a -> 'a -> bool) -> 'a List -> 'a List List *)
  (runs' R (a::b::xs) =
    if ~(R a b) then desc' R b [a] xs
    else asc' R b (CONS a) xs) /\
  (runs' R [x] = [[x]]) /\
  (runs' R [] = [])
  /\
  (* desc' :: ('a -> 'a -> bool) -> 'a -> 'a List -> 'a List -> 'a List List *)
  (desc' R a as (b::bs) = 
    if ~(R a b) then 
      desc' R b (a::as) bs
    else
      (a::as) :: runs' R (b::bs)) /\
  (desc' R a as [] = [a::as]) 
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (R,a,as,l) => LENGTH l + 1
    | INR (INL (R, l)) => LENGTH l
    | INR (INR (R,a, as, l)) => LENGTH l + 1)` >>
  rw[]
End

Definition NATURAL_MERGESORT_def:
  natural_mergesort R xs = natural_mergeall R (runs' R xs)
End
(* END :: Natural mergesort definitions *)


(* START :: Equivalence theorem for merge_asc_runs_desc *)
Theorem EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm:
  (!(R : 'a -> 'a -> bool) a as bs as'.  
    (!xs. (as' xs) = as ++ xs) 
    ==> (asc R a as bs = asc' R a as' bs)) /\
  (!(R : 'a -> 'a -> bool) (xs : 'a list). runs R xs = runs' R xs) /\
  (!(R : 'a -> 'a -> bool) a as bs. desc R a as bs = desc' R a as bs)
Proof
  ho_match_mp_tac NATURAL_MERGE_ASC_RUNS_DESC_ind >>
  rpt strip_tac >>
  simp[NATURAL_MERGE_ASC_RUNS_DESC_def, NATURAL_MERGE_ASC_RUNS_DESC'_def]
  >- (rw[])
  >- (
    rw[] >>fs[]
  )
QED
(* END :: Equivalence theorem for merge_asc_runs_desc *)

(* START :: Natural mergesort correctness sortedness theorems *)
Theorem EVERY_SORTED_ASC_RUNS_DESC_lemma:
  (* EFFICIENCY NOTICE :: use of ++ instead of the suggested (a:) compositions *)
  (!(R:'a -> 'a -> bool) a as bs.
    (transitive R /\ total R /\ SORTED R (as ++ [a]) ==>
    EVERY (SORTED R) (asc R a as bs))) /\
  (!(R:'a -> 'a -> bool) xs.
    ((total R /\ transitive R) ==> EVERY (SORTED R) (runs R xs))) /\
  (!(R:'a -> 'a -> bool) a as bs.
    transitive R /\ total R /\ SORTED R (a::as) ==>
    EVERY (SORTED R) (desc R a as bs))
Proof
  ho_match_mp_tac NATURAL_MERGE_ASC_RUNS_DESC_ind >>
  rw[]
  >- (
      rw[NATURAL_MERGE_ASC_RUNS_DESC_def] >>
      fs[] >>
      first_x_assum match_mp_tac >>
      rw[SORTED_APPEND_GEN]
    )
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
  >- (
      rw[NATURAL_MERGE_ASC_RUNS_DESC_def] >>
      metis_tac[total_def, transitive_def]
    )
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
  >- (
      rw[NATURAL_MERGE_ASC_RUNS_DESC_def] >>
      metis_tac[total_def, transitive_def]
    )
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
QED

Theorem MEM_NATURAL_MERGEAUXILLARY_lemma:
  !R xs ys. (MEM x (natural_mergeauxillary R xs ys)) = ((MEM x xs) \/ (MEM x ys))
Proof
  ho_match_mp_tac NATURAL_MERGEAUXILLARY_ind >>
  rpt strip_tac
  >- (simp[NATURAL_MERGEAUXILLARY_def])
  >- (simp[NATURAL_MERGEAUXILLARY_def])
  >- (
      rw[NATURAL_MERGEAUXILLARY_def] >>
      metis_tac[]
    )
QED

Theorem SORTED_NATURAL_MERGEAUXILLARY_lemma:
  !R xs ys. (transitive R /\ total R) ==> (SORTED R (natural_mergeauxillary R xs ys) <=> (SORTED R xs) /\ (SORTED R ys))
Proof
  ho_match_mp_tac NATURAL_MERGEAUXILLARY_ind >>
  rpt strip_tac
  >- (simp[NATURAL_MERGEAUXILLARY_def])
  >- (simp[NATURAL_MERGEAUXILLARY_def])
  >- (
      rw[NATURAL_MERGEAUXILLARY_def]
      >- (
          fs[SORTED_EQ] >>
          rw[EQ_IMP_THM]
          >- (fs[MEM_NATURAL_MERGEAUXILLARY_lemma])
          >- (
              fs[MEM_NATURAL_MERGEAUXILLARY_lemma] >>
              metis_tac[transitive_def, total_def]
            )
        )
      >- (
          fs[SORTED_EQ] >>
          rw[EQ_IMP_THM]
          >- (fs[MEM_NATURAL_MERGEAUXILLARY_lemma])
          >- (
              fs[MEM_NATURAL_MERGEAUXILLARY_lemma] >>
              metis_tac[transitive_def, total_def]
            )
        )
    )
QED

Theorem SORTED_NATURAL_MERGEADJACENT_lemma:
  !R xss. (transitive R /\ total R) ==> ((EVERY (SORTED R) (natural_mergeadjacent R xss)) <=> EVERY (SORTED R) xss)
Proof
  ho_match_mp_tac NATURAL_MERGEADJACENT_ind >>
  rpt strip_tac
  >- (simp[NATURAL_MERGEADJACENT_def])
  >- (simp[NATURAL_MERGEADJACENT_def])
  >- (
      rw[NATURAL_MERGEADJACENT_def] >>
      fs[SORTED_NATURAL_MERGEAUXILLARY_lemma] >>
      metis_tac[]
    )
QED

Theorem SORTED_NATURAL_MERGEALL_lemma:
  !R xss. (transitive R /\ total R) ==> (SORTED R (natural_mergeall R xss) <=> EVERY (SORTED R) xss)
Proof
  ho_match_mp_tac NATURAL_MERGEALL_ind >>
  rpt strip_tac
  >- (simp[NATURAL_MERGEALL_def])
  >- (simp[NATURAL_MERGEALL_def])
  >- (
      rw[NATURAL_MERGEALL_def] >>
      simp[SORTED_NATURAL_MERGEADJACENT_lemma]
    )
QED

Theorem CORRECTNESS_SORTED_NATURAL_MERGESORT:
  !R xs. (transitive R /\ total R) ==> SORTED R (natural_mergesort R xs)
Proof
  simp[NATURAL_MERGESORT_def] >>
  rw[SORTED_NATURAL_MERGEALL_lemma] >>
  simp[GSYM EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm] >>
  simp[EVERY_SORTED_ASC_RUNS_DESC_lemma]
QED

(*
Theorem CORRECTNESS_SORTED_NATURAL_MERGESORT:
  !R xs. (transitive R /\ total R) ==> SORTED R (natural_mergesort R xs)
Proof
  simp[NATURAL_MERGESORT_def] >>
  rpt strip_tac >>
  Induct_on `xs`
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def, NATURAL_MERGEALL_def])
  >- (
      rw[NATURAL_MERGE_ASC_RUNS_DESC_def, NATURAL_MERGEALL_def] >>
      Induct_on `xs`
      >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def, NATURAL_MERGEALL_def])
      >- (
          rw[NATURAL_MERGE_ASC_RUNS_DESC_def, NATURAL_MERGEALL_def]
          >- (
              simp[SORTED_NATURAL_MERGEALL_lemma] >>
              qspecl_then [`R`, `h'`, `[h]`, `xs`] assume_tac (CONJUNCT2 (CONJUNCT2 EVERY_SORTED_ASC_RUNS_DESC_lemma)) >>
              first_x_assum match_mp_tac >>
              fs[total_def] >>
              metis_tac[total_def]
            )
          >- (
              simp[SORTED_NATURAL_MERGEALL_lemma] >>
              qspecl_then [`R`, `h'`, `[h]`, `xs`] assume_tac (CONJUNCT1 EVERY_SORTED_ASC_RUNS_DESC_lemma) >>
              first_x_assum match_mp_tac >>
              fs[]
            )
        )
    )
QED
*)
(* END :: Natural mergesort correctness sortedness theorems *)

(* START :: Natural mergesort correctness mset theorems *)
Theorem MSET_FLAT_ASC_RUNS_DESC_lemma:
  (!(R: 'a -> 'a -> bool) a as bs. LIST_TO_BAG (FLAT (asc R a as bs)) = LIST_TO_BAG (as ++ [a] ++ bs)) /\
  (!(R: 'a -> 'a -> bool) xs. LIST_TO_BAG (FLAT (runs R xs)) = LIST_TO_BAG xs ) /\
  (!(R: 'a -> 'a -> bool) a as bs. LIST_TO_BAG (FLAT (desc R a as bs)) = LIST_TO_BAG (a::as ++ bs))
Proof
  ho_match_mp_tac NATURAL_MERGE_ASC_RUNS_DESC_ind >>
  rpt strip_tac
  >- ( 
      simp[NATURAL_MERGE_ASC_RUNS_DESC_def] >>
      rw[]
      >- (
          `[a'] ++ bs = a'::bs` by simp[] >>
          `(as ++ [a] ++ [a'] ++ bs) = (as ++ [a] ++ ([a'] ++ bs))` by rw[] >>
          pop_assum (fn x => pure_rewrite_tac[x]) >>
          pop_assum (fn x => pure_rewrite_tac[x]) >>
          REFL_TAC
        )
      >- (fs[LIST_TO_BAG_APPEND])
    )
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
  >- (
      rw[NATURAL_MERGE_ASC_RUNS_DESC_def]
      >- (simp[BAG_INSERT_commutes])
      >- (fs[])
    )
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
  >- (
      simp[NATURAL_MERGE_ASC_RUNS_DESC_def] >>
      rw[]
      >- (
          fs[] >>
          simp[BAG_INSERT_UNION, LIST_TO_BAG_APPEND] >>
          simp[AC ASSOC_BAG_UNION COMM_BAG_UNION]
        )
      >- (fs[LIST_TO_BAG_APPEND])
    )
  >- (simp[NATURAL_MERGE_ASC_RUNS_DESC_def])
QED

Theorem FLAT_NATURAL_MERGEAUXILLARY_lemma:
  !R xs ys. LIST_TO_BAG (natural_mergeauxillary R xs ys) = BAG_UNION (LIST_TO_BAG xs) (LIST_TO_BAG ys)
Proof
  ho_match_mp_tac NATURAL_MERGEAUXILLARY_ind >>
  rpt strip_tac
  >- (simp[NATURAL_MERGEAUXILLARY_def])
  >- (simp[NATURAL_MERGEAUXILLARY_def])
  >- (
      fs[NATURAL_MERGEAUXILLARY_def] >>
      rw[]
      >- (simp[BAG_UNION_INSERT])
      >- (
          simp[BAG_UNION_INSERT] >>
          metis_tac[ASSOC_BAG_UNION, COMM_BAG_UNION, BAG_INSERT_commutes]
        )
    )
QED

Theorem FLAT_NATURAL_MERGEADJACENT_lemma:
  !R xss. LIST_TO_BAG (FLAT (natural_mergeadjacent R xss)) = LIST_TO_BAG (FLAT xss)
Proof
  ho_match_mp_tac NATURAL_MERGEADJACENT_ind >>
  rpt strip_tac
  >- (simp[NATURAL_MERGEADJACENT_def])
  >- (simp[NATURAL_MERGEADJACENT_def])
  >- (
      fs[LIST_TO_BAG_APPEND, NATURAL_MERGEADJACENT_def, NATURAL_MERGEAUXILLARY_def] >>
      metis_tac[FLAT_NATURAL_MERGEAUXILLARY_lemma]
    )
QED

Theorem FLAT_NATURAL_MERGEALL_lemma:
  !R xss. LIST_TO_BAG (natural_mergeall R xss) = LIST_TO_BAG (FLAT xss)
Proof
  ho_match_mp_tac NATURAL_MERGEALL_ind >>
  rpt strip_tac
  >- (simp[NATURAL_MERGEALL_def])
  >- (simp[NATURAL_MERGEALL_def])
  >- (
      rw[NATURAL_MERGEALL_def] >>
      simp[FLAT_NATURAL_MERGEADJACENT_lemma]
    )
QED

Theorem CORRECTNESS_MSET_NATURAL_MERGESORT:
  !R xs. LIST_TO_BAG (natural_mergesort R xs) = LIST_TO_BAG xs
Proof
  simp[NATURAL_MERGESORT_def] >>
  rw[FLAT_NATURAL_MERGEALL_lemma] >>
  qspecl_then [`R`,`xs`] assume_tac (CONJUNCT1 (CONJUNCT2 MSET_FLAT_ASC_RUNS_DESC_lemma)) >>
  fs[EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm]
QED
(* END :: Natural mergesort correctness mset theorems *)

val _ = export_theory ()
