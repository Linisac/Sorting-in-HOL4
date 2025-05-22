open listTheory arithmeticTheory bossLib;

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
        REFL_TAC
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

(* not working... need to show termination *)
Definition quicksort_def:
  (quicksort R [] = []) /\
  (quicksort R (x::xs) =
    quicksort R (FILTER (\y. R y x) xs ++ [x] ++ quicksort R (FILTER (\y. ~R y x) xs)))
Termination
  cheat
End

(*===============================*
 *===== Top-Down Merge Sort =====*
 *===============================*)

Definition mergeaux_def:
  (mergeaux R [] ys = ys) /\
  (mergeaux R xs [] = xs) /\
  (mergeaux R (x::xs) (y::ys) =
    if R x y then
      x::(mergeaux R xs (y::ys))
    else
      y::(mergeaux R (x::xs) ys))
End

(* not working... need to show termination *)
Definition mergesort_def:
  mergesort R xs = (let n = (LENGTH xs) in (
      if n <= 1 then xs
      else mergeaux R (mergesort R (TAKE (n DIV 2) xs)) ( mergesort R (DROP (n DIV 2) xs) )
    )
  )
Termination
  cheat
End

(*================================*
 *===== Bottom-Up Merge Sort =====*
 *================================*)

Definition mergeadj_def:
  (mergeadj R [] = []) /\
  (mergeadj R [xs] = [xs]) /\
  (mergeadj R (x::y::zs) = (mergeaux R x y) :: (mergeadj R zs))
End

(* not working... need to show termination *)
Definition mergeall_def:
  (mergeall R [] = []) /\
  (mergeall R [xs] = xs) /\
  (mergeall R xss = mergeall R (mergeadj R xss))
Termination
  cheat
End

Definition mergesort_def':
  mergesort R xs = mergeall R (MAP (\x. [x]) xs)
End

