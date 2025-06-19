signature quicksortCorrectnessTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val CORRECTNESS_MSET_QUICKSORT_thm : thm
    val CORRECTNESS_SORTED_QUICKSORT_thm : thm
    val MEM_QUICKSORT_lemma : thm
    val QUICKSORT_def : thm
    val QUICKSORT_ind : thm
(*
   [container] Parent theory of "quicksortCorrectness"
   
   [CORRECTNESS_MSET_QUICKSORT_thm]  Theorem
      
      ⊢ ∀R xs. LIST_TO_BAG (quicksort R xs) = LIST_TO_BAG xs
   
   [CORRECTNESS_SORTED_QUICKSORT_thm]  Theorem
      
      ⊢ ∀R xs. total R ∧ transitive R ⇒ SORTED R (quicksort R xs)
   
   [MEM_QUICKSORT_lemma]  Theorem
      
      ⊢ ∀R xs. MEM x (quicksort R xs) ⇔ MEM x xs
   
   [QUICKSORT_def]  Theorem
      
      ⊢ (∀R. quicksort R [] = []) ∧
        ∀xs x R.
          quicksort R (x::xs) =
          quicksort R (FILTER (λy. R y x) xs) ⧺ [x] ⧺
          quicksort R (FILTER (λy. ¬R y x) xs)
   
   [QUICKSORT_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧
            (∀R x xs.
               P R (FILTER (λy. ¬R y x) xs) ∧ P R (FILTER (λy. R y x) xs) ⇒
               P R (x::xs)) ⇒
            ∀v v1. P v v1
   
   
*)
end
