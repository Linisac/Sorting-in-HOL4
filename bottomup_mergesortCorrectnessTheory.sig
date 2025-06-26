signature bottomup_mergesortCorrectnessTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val BOTTOM_UP_MERGESORT_def : thm
  
  (*  Theorems  *)
    val BOTTOM_UP_MERGEADJACENT_def : thm
    val BOTTOM_UP_MERGEADJACENT_ind : thm
    val BOTTOM_UP_MERGEALL_MAP_lemma : thm
    val BOTTOM_UP_MERGEALL_def : thm
    val BOTTOM_UP_MERGEALL_ind : thm
    val BOTTOM_UP_MERGEAUXILLARY_def : thm
    val BOTTOM_UP_MERGEAUXILLARY_ind : thm
    val CORRECTNESS_MSET_BOTTOM_UP_MERGESORT_thm : thm
    val CORRECTNESS_SORTED_BOTTOM_UP_MERGESORT_thm : thm
    val MEM_BOTTOM_UP_MERGEAUXILLARY_lemma : thm
    val MSET_BOTTOM_UP_MERGEADJACENT_lemma : thm
    val MSET_BOTTOM_UP_MERGEALL_lemma : thm
    val MSET_BOTTOM_UP_MERGEAUXILLARY_lemma : thm
    val SORTED_BOTTOM_UP_MERGEADJACENT_lemma : thm
    val SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma : thm
(*
   [container] Parent theory of "bottomup_mergesortCorrectness"
   
   [BOTTOM_UP_MERGESORT_def]  Definition
      
      ⊢ ∀R xs.
          bottom_up_mergesort R xs =
          bottom_up_mergeall R (MAP (λx. [x]) xs)
   
   [BOTTOM_UP_MERGEADJACENT_def]  Theorem
      
      ⊢ (∀R. bottom_up_mergeadjacent R [] = []) ∧
        (∀xs R. bottom_up_mergeadjacent R [xs] = [xs]) ∧
        ∀ys xs lst R.
          bottom_up_mergeadjacent R (xs::ys::lst) =
          bottom_up_mergeauxillary R xs ys::bottom_up_mergeadjacent R lst
   
   [BOTTOM_UP_MERGEADJACENT_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧ (∀R xs. P R [xs]) ∧
            (∀R xs ys lst. P R lst ⇒ P R (xs::ys::lst)) ⇒
            ∀v v1. P v v1
   
   [BOTTOM_UP_MERGEALL_MAP_lemma]  Theorem
      
      ⊢ ∀R xss.
          transitive R ∧ total R ⇒
          (SORTED R (bottom_up_mergeall R xss) ⇔ EVERY (SORTED R) xss)
   
   [BOTTOM_UP_MERGEALL_def]  Theorem
      
      ⊢ (∀R. bottom_up_mergeall R [] = []) ∧
        (∀xs R. bottom_up_mergeall R [xs] = xs) ∧
        ∀v7 v6 v2 R.
          bottom_up_mergeall R (v2::v6::v7) =
          bottom_up_mergeall R (bottom_up_mergeadjacent R (v2::v6::v7))
   
   [BOTTOM_UP_MERGEALL_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧ (∀R xs. P R [xs]) ∧
            (∀R v2 v6 v7.
               P R (bottom_up_mergeadjacent R (v2::v6::v7)) ⇒
               P R (v2::v6::v7)) ⇒
            ∀v v1. P v v1
   
   [BOTTOM_UP_MERGEAUXILLARY_def]  Theorem
      
      ⊢ (∀xs R. bottom_up_mergeauxillary R xs [] = xs) ∧
        (∀v5 v4 R. bottom_up_mergeauxillary R [] (v4::v5) = v4::v5) ∧
        ∀ys y xs x R.
          bottom_up_mergeauxillary R (x::xs) (y::ys) =
          if R x y then x::bottom_up_mergeauxillary R xs (y::ys)
          else y::bottom_up_mergeauxillary R (x::xs) ys
   
   [BOTTOM_UP_MERGEAUXILLARY_ind]  Theorem
      
      ⊢ ∀P. (∀R xs. P R xs []) ∧ (∀R v4 v5. P R [] (v4::v5)) ∧
            (∀R x xs y ys.
               (¬R x y ⇒ P R (x::xs) ys) ∧ (R x y ⇒ P R xs (y::ys)) ⇒
               P R (x::xs) (y::ys)) ⇒
            ∀v v1 v2. P v v1 v2
   
   [CORRECTNESS_MSET_BOTTOM_UP_MERGESORT_thm]  Theorem
      
      ⊢ ∀R xs. LIST_TO_BAG (bottom_up_mergesort R xs) = LIST_TO_BAG xs
   
   [CORRECTNESS_SORTED_BOTTOM_UP_MERGESORT_thm]  Theorem
      
      ⊢ ∀R xs. total R ∧ transitive R ⇒ SORTED R (bottom_up_mergesort R xs)
   
   [MEM_BOTTOM_UP_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          MEM x (bottom_up_mergeauxillary R xs ys) ⇔ MEM x xs ∨ MEM x ys
   
   [MSET_BOTTOM_UP_MERGEADJACENT_lemma]  Theorem
      
      ⊢ ∀R xss.
          LIST_TO_BAG (FLAT (bottom_up_mergeadjacent R xss)) =
          LIST_TO_BAG (FLAT xss)
   
   [MSET_BOTTOM_UP_MERGEALL_lemma]  Theorem
      
      ⊢ ∀R xss.
          LIST_TO_BAG (bottom_up_mergeall R xss) = LIST_TO_BAG (FLAT xss)
   
   [MSET_BOTTOM_UP_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R l1 l2.
          LIST_TO_BAG (bottom_up_mergeauxillary R l1 l2) =
          LIST_TO_BAG l1 ⊎ LIST_TO_BAG l2
   
   [SORTED_BOTTOM_UP_MERGEADJACENT_lemma]  Theorem
      
      ⊢ ∀R xss.
          transitive R ∧ total R ⇒
          (EVERY (SORTED R) (bottom_up_mergeadjacent R xss) ⇔
           EVERY (SORTED R) xss)
   
   [SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          transitive R ∧ total R ⇒
          (SORTED R (bottom_up_mergeauxillary R xs ys) ⇔
           SORTED R xs ∧ SORTED R ys)
   
   
*)
end
