open HolKernel Parse boolLib;
open bossLib;
open listTheory rich_listTheory;
open arithmeticTheory dividesTheory;

val _ = new_theory "chaptertwo";

(*==========================*
 *===== INSERTION SORT =====
 *==========================*)

Definition insertaux_def:
  (insertaux R x [] = [x]) /\
  (insertaux R x (y::ys) =
    if R x y then
      x :: (y :: ys)
    else
      y :: insertaux R x ys)
End

Definition insertionsort_def:
  (insertionsort R [] = []) /\
  (insertionsort R (x::xs) = insertaux R x (insertionsort R xs))
End

Theorem MEM_insertaux:
  MEM x (insertaux R h l) <=> (MEM x [h]) \/ (MEM x l)
Proof
  Induct_on `l`
    >- (fs[insertaux_def])
    >> fs[insertaux_def] >>
  strip_tac >>
  Cases_on `R h h'`
    >> fs[] >> metis_tac[]
QED

Theorem MEM_insertionsort:
  !R L x. MEM x (insertionsort R L) = MEM x L
Proof
  Induct_on `L`
   >- fs[insertionsort_def, insertaux_def] 
   >> fs[insertionsort_def] >> fs[MEM_insertaux]
QED

Theorem MEM_insertionsort':
  !R L x. MEM x (insertionsort R L) = MEM x L
Proof
  Induct_on `L`
    >- (
        pure_rewrite_tac[insertionsort_def] >>
        pure_rewrite_tac[MEM] >>
        pure_rewrite_tac[REFL_CLAUSE] >>
        fs[]
      )
    >- (
        pure_rewrite_tac[insertionsort_def] >>
        pure_rewrite_tac[MEM_insertaux] >> 
        pure_rewrite_tac[MEM] >> 
        pure_rewrite_tac[OR_CLAUSES] >> 
        pop_assum (fn x => pure_rewrite_tac[x]) >> 
        strip_tac >> strip_tac >> 
        fs[]
      )
QED

Theorem LENGTH_insertaux:
  LENGTH (insertaux R h l) = SUC (LENGTH l)
Proof
  Induct_on `l`
    >- ( 
         pure_rewrite_tac[insertaux_def] >>
         pure_rewrite_tac[LENGTH] >>
         REFL_TAC
        )
    >- (
         pure_rewrite_tac[insertaux_def] >>
         pure_rewrite_tac[LENGTH] >>
         Cases_on `R h h'`
           >- (
            pure_rewrite_tac[bool_case_thm] >>
            pure_rewrite_tac[LENGTH] >> REFL_TAC
          )
           >- (
            pure_rewrite_tac[bool_case_thm] >>
            pure_rewrite_tac[LENGTH] >>
            pop_assum (fn x => pure_rewrite_tac [x]) >> REFL_TAC
          )
        )
QED

Theorem LENGTH_insertionsort:
  LENGTH (insertionsort R l) = LENGTH l
Proof
  Induct_on `l`
    >- (
      pure_rewrite_tac[insertionsort_def] >> 
      REFL_TAC
    )
    >- (
      pure_rewrite_tac[insertionsort_def] >>
      pure_rewrite_tac[LENGTH] >>
      pure_rewrite_tac[LENGTH_insertaux] >>
      pop_assum (fn x => pure_rewrite_tac [x]) >>
      strip_tac >> REFL_TAC
     )
QED

(* ====================*
 *===== QUICKSORT =====*
 *=====================*)

Definition quicksort_def:
  (quicksort R [] = []) /\
  (quicksort R (x::xs) =
    quicksort R (FILTER (\y. R y x) xs) ++ [x] ++ quicksort R (FILTER (\y. ~R y x) xs))
Termination
  WF_REL_TAC `measure (\x. LENGTH (SND x))` >>
  rw[LENGTH]
  >- ( 
        qspecl_then [`(\y. ~(R y x))`,`xs`] assume_tac LENGTH_FILTER_LEQ >>
        decide_tac
    )
  >- (
        qspecl_then [`(\y. R y x)`, `xs`] assume_tac LENGTH_FILTER_LEQ >>
        decide_tac
    )
End

(*===============================*
 *===== Top-Down Merge Sort =====*
 *===============================*)

Theorem LEQ_TWO_DIV_LEQ_ZERO:
  !n. n >= 2 ==> n DIV 2 > 0
Proof
  strip_tac >>
  disch_tac >>
  qspecl_then [`1`, `n`, `2`] assume_tac X_LE_DIV >>
  fs[]
QED

Theorem LENGTH_DIV_TWO_LT:
  LENGTH l >= 2 ==> LENGTH l DIV 2 < LENGTH l
Proof
  rpt strip_tac >>
  match_mp_tac DIV_LESS >>
  simp[]
QED

Definition mergeaux_def:
  (mergeaux R [] ys = ys) /\
  (mergeaux R xs [] = xs) /\
  (mergeaux R (x::xs) (y::ys) =
    if R x y then
      x::(mergeaux R xs (y::ys))
    else
      y::(mergeaux R (x::xs) ys))
End

Definition mergesort_def:
  mergesort R xs = (let n = (LENGTH xs) in (
      if n <= 1 then xs
      else mergeaux R (mergesort R (TAKE (n DIV 2) xs)) ( mergesort R (DROP (n DIV 2) xs) )
    )
  )
Termination
  WF_REL_TAC `measure (\x . LENGTH (SND x))` >>
  rw[LENGTH_TAKE, LENGTH_DROP]
  >- (
    `LENGTH xs >= 2` by decide_tac >>
    qspecl_then [`LENGTH xs`] assume_tac LEQ_TWO_DIV_LEQ_ZERO >>
    res_tac >> res_tac >>
    pure_rewrite_tac[GSYM GREATER_DEF] >>
    res_tac
    )
  >- (
    `LENGTH xs >= 2` by decide_tac >>
    `LENGTH xs DIV 2 < LENGTH xs` by (
        match_mp_tac DIV_LESS >>
        decide_tac 
      ) >>
    qspecl_then [`LENGTH xs DIV 2`, `xs`] assume_tac LENGTH_TAKE >>
    `LENGTH xs DIV 2 <= LENGTH xs` by decide_tac >>
    res_tac >>
    pop_assum (fn x => pure_rewrite_tac[x]) >>
    (* need to reorder assumptions... will use fs[] instead *)
    fs[]
    )
End

(*================================*
 *===== Bottom-Up Merge Sort =====*
 *================================*)

Definition mergeadj_def:
  (mergeadj R [] = []) /\
  (mergeadj R [xs] = [xs]) /\
  (mergeadj R (x::y::zs) = (mergeaux R x y) :: (mergeadj R zs))
End

Theorem LENGTH_mergeaux:
  !R l. LENGTH (mergeadj R l) < SUC (LENGTH l)
Proof
  ho_match_mp_tac mergeadj_ind >>
  rw[mergeadj_def]
  (* There's no need to split cases *)
QED

Definition mergeall_def:
  (mergeall R [] = []) /\
  (mergeall R [xs] = xs) /\
  (mergeall R xss = mergeall R (mergeadj R xss))
Termination
  WF_REL_TAC `measure (LENGTH o SND)` >>
  pure_rewrite_tac[LENGTH, mergeadj_def, mergeaux_def] >>
  rpt strip_tac >>
  rw[] >> 
  metis_tac[LENGTH_mergeaux]
End

Definition mergesort_def':
  mergesort R xs = mergeall R (MAP (\x. [x]) xs)
End

(*==============================*
 *===== Natural Merge Sort =====*
 *==============================*)

Definition naturalaux_def:
  (asc R a as [] = [ (as [a]) ]) /\
  (asc R a as (b::bs) =
    if ~(R a b) then
      asc R b (as o CONS a) bs
    else
      as [a] :: runs R (b::bs) )
  /\
  (runs R [] = []) /\
  (runs R [x] = [[x]]) /\
  (runs R (a::b::xs) =
    if R a b then
      desc R b [a] xs
    else
      asc R b (CONS a) xs)
  /\
  (desc R a as [] = [a::as]) /\
  (desc R a as (b::bs) = 
    if R a b then 
      desc R b (a::as) bs
    else
      (a::as) :: runs R (b::bs))
Termination
  WF_REL_TAC `measure (\x. case x of
      | INL (R,a,as,l) => list_size foo l + 1
      | INR (INL (R, l)) => list_size foo l
      | INR (INR (R,a, as, l)) => list_size foo l + 1
    )` >>
  rw[]
End

Definition naturalmerge_def:
  naturalmerge R xs = mergeall R (runs R xs)
End

val _ = export_theory();
