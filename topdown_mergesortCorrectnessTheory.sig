signature topdown_mergesortCorrectnessTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val CORRECTNESS_MSET_TOP_DOWN_MERGESORT_thm : thm
    val CORRECTNESS_SORTED_TOP_DOWN_MERGESORT_thm : thm
    val MEM_TOP_DOWN_MERGEAUXILLARY_lemma : thm
    val MSET_MERGEAUXILLARY_lemma : thm
    val SORTED_MERGEAUXILLARY_lemma : thm
    val TOP_DOWN_MERGEAUXILLARY_def : thm
    val TOP_DOWN_MERGEAUXILLARY_ind : thm
    val TOP_DOWN_MERGESORT_def : thm
    val TOP_DOWN_MERGESORT_ind : thm
(*
   [container] Parent theory of "topdown_mergesortCorrectness"
   
   [CORRECTNESS_MSET_TOP_DOWN_MERGESORT_thm]  Theorem
      
      ⊢ ∀R xs. LIST_TO_BAG (top_down_mergesort R xs) = LIST_TO_BAG xs
   
   [CORRECTNESS_SORTED_TOP_DOWN_MERGESORT_thm]  Theorem
      
      ⊢ ∀R xs. total R ∧ transitive R ⇒ SORTED R (top_down_mergesort R xs)
   
   [MEM_TOP_DOWN_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          MEM x (top_down_mergeauxillary R xs ys) ⇔ MEM x xs ∨ MEM x ys
   
   [MSET_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          LIST_TO_BAG (top_down_mergeauxillary R xs ys) =
          LIST_TO_BAG xs ⊎ LIST_TO_BAG ys
   
   [SORTED_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          transitive R ∧ total R ⇒
          (SORTED R (top_down_mergeauxillary R xs ys) ⇔
           SORTED R xs ∧ SORTED R ys)
   
   [TOP_DOWN_MERGEAUXILLARY_def]  Theorem
      
      ⊢ (∀xs R. top_down_mergeauxillary R xs [] = xs) ∧
        (∀v5 v4 R. top_down_mergeauxillary R [] (v4::v5) = v4::v5) ∧
        ∀ys y xs x R.
          top_down_mergeauxillary R (x::xs) (y::ys) =
          if R x y then x::top_down_mergeauxillary R xs (y::ys)
          else y::top_down_mergeauxillary R (x::xs) ys
   
   [TOP_DOWN_MERGEAUXILLARY_ind]  Theorem
      
      ⊢ ∀P. (∀R xs. P R xs []) ∧ (∀R v4 v5. P R [] (v4::v5)) ∧
            (∀R x xs y ys.
               (¬R x y ⇒ P R (x::xs) ys) ∧ (R x y ⇒ P R xs (y::ys)) ⇒
               P R (x::xs) (y::ys)) ⇒
            ∀v v1 v2. P v v1 v2
   
   [TOP_DOWN_MERGESORT_def]  Theorem
      
      ⊢ (∀R. top_down_mergesort R [] = []) ∧
        (∀x R. top_down_mergesort R [x] = [x]) ∧
        ∀v7 v6 v2 R.
          top_down_mergesort R (v2::v6::v7) =
          top_down_mergeauxillary R
            (top_down_mergesort R
               (TAKE (LENGTH (v2::v6::v7) DIV 2) (v2::v6::v7)))
            (top_down_mergesort R
               (DROP (LENGTH (v2::v6::v7) DIV 2) (v2::v6::v7)))
   
   [TOP_DOWN_MERGESORT_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧ (∀R x. P R [x]) ∧
            (∀R v2 v6 v7.
               P R (DROP (LENGTH (v2::v6::v7) DIV 2) (v2::v6::v7)) ∧
               P R (TAKE (LENGTH (v2::v6::v7) DIV 2) (v2::v6::v7)) ⇒
               P R (v2::v6::v7)) ⇒
            ∀v v1. P v v1
   
   
*)
end
