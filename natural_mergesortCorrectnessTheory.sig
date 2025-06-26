signature natural_mergesortCorrectnessTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val NATURAL_MERGESORT_def : thm
    val NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract0 : thm
    val NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract1 : thm
    val NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract2 : thm
    val NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_primitive : thm
    val NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract0 : thm
    val NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract1 : thm
    val NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract2 : thm
    val NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_primitive : thm
  
  (*  Theorems  *)
    val CORRECTNESS_MSET_NATURAL_MERGESORT : thm
    val CORRECTNESS_SORTED_NATURAL_MERGESORT : thm
    val EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm : thm
    val EVERY_SORTED_ASC_RUNS_DESC_lemma : thm
    val FLAT_NATURAL_MERGEADJACENT_lemma : thm
    val FLAT_NATURAL_MERGEALL_lemma : thm
    val FLAT_NATURAL_MERGEAUXILLARY_lemma : thm
    val MEM_NATURAL_MERGEAUXILLARY_lemma : thm
    val MSET_FLAT_ASC_RUNS_DESC_lemma : thm
    val NATURAL_MERGEADJACENT_def : thm
    val NATURAL_MERGEADJACENT_ind : thm
    val NATURAL_MERGEALL_def : thm
    val NATURAL_MERGEALL_ind : thm
    val NATURAL_MERGEAUXILLARY_def : thm
    val NATURAL_MERGEAUXILLARY_ind : thm
    val NATURAL_MERGE_ASC_RUNS_DESC'_def : thm
    val NATURAL_MERGE_ASC_RUNS_DESC'_ind : thm
    val NATURAL_MERGE_ASC_RUNS_DESC_def : thm
    val NATURAL_MERGE_ASC_RUNS_DESC_ind : thm
    val SORTED_NATURAL_MERGEADJACENT_lemma : thm
    val SORTED_NATURAL_MERGEALL_lemma : thm
    val SORTED_NATURAL_MERGEAUXILLARY_lemma : thm
(*
   [container] Parent theory of "natural_mergesortCorrectness"
   
   [NATURAL_MERGESORT_def]  Definition
      
      ⊢ ∀R xs. natural_mergesort R xs = natural_mergeall R (runs' R xs)
   
   [NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1 x2.
          asc' x x0 x1 x2 =
          NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION (INL (x,x0,x1,x2))
   
   [NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0.
          runs' x x0 =
          NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION (INR (INL (x,x0)))
   
   [NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract2]  Definition
      
      ⊢ ∀x x0 x1 x2.
          desc' x x0 x1 x2 =
          NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION (INR (INR (x,x0,x1,x2)))
   
   [NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_primitive]  Definition
      
      ⊢ NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION =
        WFREC
          (@R'.
             WF R' ∧
             (∀bs as b a R.
                R a b ⇒ R' (INL (R,b,as ∘ CONS a,bs)) (INL (R,a,as,b::bs))) ∧
             (∀as bs b a R.
                ¬R a b ⇒ R' (INR (INL (R,b::bs))) (INL (R,a,as,b::bs))) ∧
             (∀xs b a R.
                ¬R a b ⇒
                R' (INR (INR (R,b,[a],xs))) (INR (INL (R,a::b::xs)))) ∧
             (∀xs b a R.
                ¬¬R a b ⇒ R' (INL (R,b,CONS a,xs)) (INR (INL (R,a::b::xs)))) ∧
             (∀as bs b a R.
                ¬¬R a b ⇒
                R' (INR (INL (R,b::bs))) (INR (INR (R,a,as,b::bs)))) ∧
             ∀bs as b a R.
               ¬R a b ⇒
               R' (INR (INR (R,b,a::as,bs))) (INR (INR (R,a,as,b::bs))))
          (λNATURAL_MERGE_ASC_RUNS_DESC'_def_UNION a'.
               case a' of
                 INL (R,a,as,[]) => I [as [a]]
               | INL (R,a,as,b::bs) =>
                 I
                   (if R a b then
                      NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION
                        (INL (R,b,as ∘ CONS a,bs))
                    else
                      as [a]::
                        NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION
                          (INR (INL (R,b::bs))))
               | INR (INL (R',[])) => I []
               | INR (INL (R',[a''])) => I [[a'']]
               | INR (INL (R',a''::b'::xs)) =>
                 I
                   (if (¬R' a'' b') then
                      NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION
                        (INR (INR (R',b',[a''],xs)))
                    else
                      NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION
                        (INL (R',b',CONS a'',xs)))
               | INR (INR (R'',a'³',as',[])) => I [a'³'::as']
               | INR (INR (R'',a'³',as',b''::bs')) =>
                 I
                   (if (¬R'' a'³' b'') then
                      NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION
                        (INR (INR (R'',b'',a'³'::as',bs')))
                    else
                      (a'³'::as')::
                        NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION
                          (INR (INL (R'',b''::bs')))))
   
   [NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1 x2.
          asc x x0 x1 x2 =
          NATURAL_MERGE_ASC_RUNS_DESC_def_UNION (INL (x,x0,x1,x2))
   
   [NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0.
          runs x x0 =
          NATURAL_MERGE_ASC_RUNS_DESC_def_UNION (INR (INL (x,x0)))
   
   [NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract2]  Definition
      
      ⊢ ∀x x0 x1 x2.
          desc x x0 x1 x2 =
          NATURAL_MERGE_ASC_RUNS_DESC_def_UNION (INR (INR (x,x0,x1,x2)))
   
   [NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_primitive]  Definition
      
      ⊢ NATURAL_MERGE_ASC_RUNS_DESC_def_UNION =
        WFREC
          (@R'.
             WF R' ∧
             (∀bs as b a R.
                R a b ⇒ R' (INL (R,b,as ⧺ [a],bs)) (INL (R,a,as,b::bs))) ∧
             (∀as bs b a R.
                ¬R a b ⇒ R' (INR (INL (R,b::bs))) (INL (R,a,as,b::bs))) ∧
             (∀xs b a R.
                ¬R a b ⇒
                R' (INR (INR (R,b,[a],xs))) (INR (INL (R,a::b::xs)))) ∧
             (∀xs b a R.
                ¬¬R a b ⇒ R' (INL (R,b,[a],xs)) (INR (INL (R,a::b::xs)))) ∧
             (∀as bs b a R.
                ¬¬R a b ⇒
                R' (INR (INL (R,b::bs))) (INR (INR (R,a,as,b::bs)))) ∧
             ∀bs as b a R.
               ¬R a b ⇒
               R' (INR (INR (R,b,a::as,bs))) (INR (INR (R,a,as,b::bs))))
          (λNATURAL_MERGE_ASC_RUNS_DESC_def_UNION a'.
               case a' of
                 INL (R,a,as,[]) => I [as ⧺ [a]]
               | INL (R,a,as,b::bs) =>
                 I
                   (if R a b then
                      NATURAL_MERGE_ASC_RUNS_DESC_def_UNION
                        (INL (R,b,as ⧺ [a],bs))
                    else
                      (as ⧺ [a])::
                        NATURAL_MERGE_ASC_RUNS_DESC_def_UNION
                          (INR (INL (R,b::bs))))
               | INR (INL (R',[])) => I []
               | INR (INL (R',[a''])) => I [[a'']]
               | INR (INL (R',a''::b'::xs)) =>
                 I
                   (if (¬R' a'' b') then
                      NATURAL_MERGE_ASC_RUNS_DESC_def_UNION
                        (INR (INR (R',b',[a''],xs)))
                    else
                      NATURAL_MERGE_ASC_RUNS_DESC_def_UNION
                        (INL (R',b',[a''],xs)))
               | INR (INR (R'',a'³',as',[])) => I [a'³'::as']
               | INR (INR (R'',a'³',as',b''::bs')) =>
                 I
                   (if (¬R'' a'³' b'') then
                      NATURAL_MERGE_ASC_RUNS_DESC_def_UNION
                        (INR (INR (R'',b'',a'³'::as',bs')))
                    else
                      (a'³'::as')::
                        NATURAL_MERGE_ASC_RUNS_DESC_def_UNION
                          (INR (INL (R'',b''::bs')))))
   
   [CORRECTNESS_MSET_NATURAL_MERGESORT]  Theorem
      
      ⊢ ∀R xs. LIST_TO_BAG (natural_mergesort R xs) = LIST_TO_BAG xs
   
   [CORRECTNESS_SORTED_NATURAL_MERGESORT]  Theorem
      
      ⊢ ∀R xs. transitive R ∧ total R ⇒ SORTED R (natural_mergesort R xs)
   
   [EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm]  Theorem
      
      ⊢ (∀R a as bs as'.
           (∀xs. as' xs = as ⧺ xs) ⇒ asc R a as bs = asc' R a as' bs) ∧
        (∀R xs. runs R xs = runs' R xs) ∧
        ∀R a as bs. desc R a as bs = desc' R a as bs
   
   [EVERY_SORTED_ASC_RUNS_DESC_lemma]  Theorem
      
      ⊢ (∀R a as bs.
           transitive R ∧ total R ∧ SORTED R (as ⧺ [a]) ⇒
           EVERY (SORTED R) (asc R a as bs)) ∧
        (∀R xs. total R ∧ transitive R ⇒ EVERY (SORTED R) (runs R xs)) ∧
        ∀R a as bs.
          transitive R ∧ total R ∧ SORTED R (a::as) ⇒
          EVERY (SORTED R) (desc R a as bs)
   
   [FLAT_NATURAL_MERGEADJACENT_lemma]  Theorem
      
      ⊢ ∀R xss.
          LIST_TO_BAG (FLAT (natural_mergeadjacent R xss)) =
          LIST_TO_BAG (FLAT xss)
   
   [FLAT_NATURAL_MERGEALL_lemma]  Theorem
      
      ⊢ ∀R xss.
          LIST_TO_BAG (natural_mergeall R xss) = LIST_TO_BAG (FLAT xss)
   
   [FLAT_NATURAL_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          LIST_TO_BAG (natural_mergeauxillary R xs ys) =
          LIST_TO_BAG xs ⊎ LIST_TO_BAG ys
   
   [MEM_NATURAL_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          MEM x (natural_mergeauxillary R xs ys) ⇔ MEM x xs ∨ MEM x ys
   
   [MSET_FLAT_ASC_RUNS_DESC_lemma]  Theorem
      
      ⊢ (∀R a as bs.
           LIST_TO_BAG (FLAT (asc R a as bs)) = LIST_TO_BAG (as ⧺ [a] ⧺ bs)) ∧
        (∀R xs. LIST_TO_BAG (FLAT (runs R xs)) = LIST_TO_BAG xs) ∧
        ∀R a as bs.
          LIST_TO_BAG (FLAT (desc R a as bs)) = LIST_TO_BAG (a::as ⧺ bs)
   
   [NATURAL_MERGEADJACENT_def]  Theorem
      
      ⊢ (∀R. natural_mergeadjacent R [] = []) ∧
        (∀xs R. natural_mergeadjacent R [xs] = [xs]) ∧
        ∀zs y x R.
          natural_mergeadjacent R (x::y::zs) =
          natural_mergeauxillary R x y::natural_mergeadjacent R zs
   
   [NATURAL_MERGEADJACENT_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧ (∀R xs. P R [xs]) ∧
            (∀R x y zs. P R zs ⇒ P R (x::y::zs)) ⇒
            ∀v v1. P v v1
   
   [NATURAL_MERGEALL_def]  Theorem
      
      ⊢ (∀R. natural_mergeall R [] = []) ∧
        (∀xs R. natural_mergeall R [xs] = xs) ∧
        ∀v7 v6 v2 R.
          natural_mergeall R (v2::v6::v7) =
          natural_mergeall R (natural_mergeadjacent R (v2::v6::v7))
   
   [NATURAL_MERGEALL_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧ (∀R xs. P R [xs]) ∧
            (∀R v2 v6 v7.
               P R (natural_mergeadjacent R (v2::v6::v7)) ⇒
               P R (v2::v6::v7)) ⇒
            ∀v v1. P v v1
   
   [NATURAL_MERGEAUXILLARY_def]  Theorem
      
      ⊢ (∀ys R. natural_mergeauxillary R [] ys = ys) ∧
        (∀v5 v4 R. natural_mergeauxillary R (v4::v5) [] = v4::v5) ∧
        ∀ys y xs x R.
          natural_mergeauxillary R (x::xs) (y::ys) =
          if R x y then x::natural_mergeauxillary R xs (y::ys)
          else y::natural_mergeauxillary R (x::xs) ys
   
   [NATURAL_MERGEAUXILLARY_ind]  Theorem
      
      ⊢ ∀P. (∀R ys. P R [] ys) ∧ (∀R v4 v5. P R (v4::v5) []) ∧
            (∀R x xs y ys.
               (¬R x y ⇒ P R (x::xs) ys) ∧ (R x y ⇒ P R xs (y::ys)) ⇒
               P R (x::xs) (y::ys)) ⇒
            ∀v v1 v2. P v v1 v2
   
   [NATURAL_MERGE_ASC_RUNS_DESC'_def]  Theorem
      
      ⊢ (∀bs b as a R.
           asc' R a as (b::bs) =
           if R a b then asc' R b (as ∘ CONS a) bs
           else as [a]::runs' R (b::bs)) ∧
        (∀as a R. asc' R a as [] = [as [a]]) ∧
        (∀xs b a R.
           runs' R (a::b::xs) =
           if ¬R a b then desc' R b [a] xs else asc' R b (CONS a) xs) ∧
        (∀x R. runs' R [x] = [[x]]) ∧ (∀R. runs' R [] = []) ∧
        (∀bs b as a R.
           desc' R a as (b::bs) =
           if ¬R a b then desc' R b (a::as) bs
           else (a::as)::runs' R (b::bs)) ∧
        ∀as a R. desc' R a as [] = [a::as]
   
   [NATURAL_MERGE_ASC_RUNS_DESC'_ind]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀R a as b bs.
             (¬R a b ⇒ P1 R (b::bs)) ∧ (R a b ⇒ P0 R b (as ∘ CONS a) bs) ⇒
             P0 R a as (b::bs)) ∧ (∀R a as. P0 R a as []) ∧
          (∀R a b xs.
             (¬¬R a b ⇒ P0 R b (CONS a) xs) ∧ (¬R a b ⇒ P2 R b [a] xs) ⇒
             P1 R (a::b::xs)) ∧ (∀R x. P1 R [x]) ∧ (∀R. P1 R []) ∧
          (∀R a as b bs.
             (¬¬R a b ⇒ P1 R (b::bs)) ∧ (¬R a b ⇒ P2 R b (a::as) bs) ⇒
             P2 R a as (b::bs)) ∧ (∀R a as. P2 R a as []) ⇒
          (∀v0 v1 v2 v3. P0 v0 v1 v2 v3) ∧ (∀v0 v1. P1 v0 v1) ∧
          ∀v0 v1 v2 v3. P2 v0 v1 v2 v3
   
   [NATURAL_MERGE_ASC_RUNS_DESC_def]  Theorem
      
      ⊢ (∀bs b as a R.
           asc R a as (b::bs) =
           if R a b then asc R b (as ⧺ [a]) bs
           else (as ⧺ [a])::runs R (b::bs)) ∧
        (∀as a R. asc R a as [] = [as ⧺ [a]]) ∧
        (∀xs b a R.
           runs R (a::b::xs) =
           if ¬R a b then desc R b [a] xs else asc R b [a] xs) ∧
        (∀x R. runs R [x] = [[x]]) ∧ (∀R. runs R [] = []) ∧
        (∀bs b as a R.
           desc R a as (b::bs) =
           if ¬R a b then desc R b (a::as) bs else (a::as)::runs R (b::bs)) ∧
        ∀as a R. desc R a as [] = [a::as]
   
   [NATURAL_MERGE_ASC_RUNS_DESC_ind]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀R a as b bs.
             (¬R a b ⇒ P1 R (b::bs)) ∧ (R a b ⇒ P0 R b (as ⧺ [a]) bs) ⇒
             P0 R a as (b::bs)) ∧ (∀R a as. P0 R a as []) ∧
          (∀R a b xs.
             (¬¬R a b ⇒ P0 R b [a] xs) ∧ (¬R a b ⇒ P2 R b [a] xs) ⇒
             P1 R (a::b::xs)) ∧ (∀R x. P1 R [x]) ∧ (∀R. P1 R []) ∧
          (∀R a as b bs.
             (¬¬R a b ⇒ P1 R (b::bs)) ∧ (¬R a b ⇒ P2 R b (a::as) bs) ⇒
             P2 R a as (b::bs)) ∧ (∀R a as. P2 R a as []) ⇒
          (∀v0 v1 v2 v3. P0 v0 v1 v2 v3) ∧ (∀v0 v1. P1 v0 v1) ∧
          ∀v0 v1 v2 v3. P2 v0 v1 v2 v3
   
   [SORTED_NATURAL_MERGEADJACENT_lemma]  Theorem
      
      ⊢ ∀R xss.
          transitive R ∧ total R ⇒
          (EVERY (SORTED R) (natural_mergeadjacent R xss) ⇔
           EVERY (SORTED R) xss)
   
   [SORTED_NATURAL_MERGEALL_lemma]  Theorem
      
      ⊢ ∀R xss.
          transitive R ∧ total R ⇒
          (SORTED R (natural_mergeall R xss) ⇔ EVERY (SORTED R) xss)
   
   [SORTED_NATURAL_MERGEAUXILLARY_lemma]  Theorem
      
      ⊢ ∀R xs ys.
          transitive R ∧ total R ⇒
          (SORTED R (natural_mergeauxillary R xs ys) ⇔
           SORTED R xs ∧ SORTED R ys)
   
   
*)
end
