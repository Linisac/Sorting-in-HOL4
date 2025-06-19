signature insertionsortCorrectnessTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val INSERTIONSORT_def : thm
    val INSERTION_AUXILLARY_def : thm
  
  (*  Theorems  *)
    val CORRECTNESS_SORTED_INSERTIONSORT_thm : thm
    val CORRECTNNESS_MSET_INSERTSORT : thm
    val MEM_INSERTIONAUXILLARY_lemma : thm
    val MSET_INSERTION_AUXILLARY_lemma : thm
    val SORTED_INSERTIONAUXILLARY_lemma : thm
(*
   [container] Parent theory of "insertionsortCorrectness"
   
   [INSERTIONSORT_def]  Definition
      
      ⊢ (∀R. insertionsort R [] = []) ∧
        ∀R x xs.
          insertionsort R (x::xs) =
          insertionAuxillary R x (insertionsort R xs)
   
   [INSERTION_AUXILLARY_def]  Definition
      
      ⊢ (∀R x. insertionAuxillary R x [] = [x]) ∧
        ∀R x y ys.
          insertionAuxillary R x (y::ys) =
          if R x y then x::y::ys else y::insertionAuxillary R x ys
   
   [CORRECTNESS_SORTED_INSERTIONSORT_thm]  Theorem
      
      ⊢ total R ∧ transitive R ⇒ SORTED R (insertionsort R xs)
   
   [CORRECTNNESS_MSET_INSERTSORT]  Theorem
      
      ⊢ LIST_TO_BAG (insertionsort R xs) = LIST_TO_BAG xs
   
   [MEM_INSERTIONAUXILLARY_lemma]  Theorem
      
      ⊢ MEM e (insertionAuxillary R x xs) ⇔ MEM e [x] ∨ MEM e xs
   
   [MSET_INSERTION_AUXILLARY_lemma]  Theorem
      
      ⊢ LIST_TO_BAG (insertionAuxillary R x xs) = LIST_TO_BAG (x::xs)
   
   [SORTED_INSERTIONAUXILLARY_lemma]  Theorem
      
      ⊢ total R ∧ transitive R ⇒
        (SORTED R (insertionAuxillary R x xs) ⇔ SORTED R xs)
   
   
*)
end
