signature chaptertwoTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val insertaux_def : thm
    val insertionsort_def : thm
    val mergesort_def' : thm
    val naturalaux_def_UNION_extract0 : thm
    val naturalaux_def_UNION_extract1 : thm
    val naturalaux_def_UNION_extract2 : thm
    val naturalaux_def_UNION_primitive : thm
    val naturalmerge_def : thm
  
  (*  Theorems  *)
    val LENGTH_DIV_TWO_LT : thm
    val LENGTH_insertaux : thm
    val LENGTH_insertionsort : thm
    val LENGTH_mergeaux : thm
    val LEQ_TWO_DIV_LEQ_ZERO : thm
    val MEM_insertaux : thm
    val MEM_insertionsort : thm
    val MEM_insertionsort' : thm
    val mergeadj_def : thm
    val mergeadj_ind : thm
    val mergeall_def : thm
    val mergeall_ind : thm
    val mergeaux_def : thm
    val mergeaux_ind : thm
    val mergesort_ind : thm
    val naturalaux_def : thm
    val naturalaux_ind : thm
    val quicksort_def : thm
    val quicksort_ind : thm
  
  val chaptertwo_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "chaptertwo"
   
   [patternMatches] Parent theory of "chaptertwo"
   
   [insertaux_def]  Definition
      
      ⊢ (∀R x. insertaux R x [] = [x]) ∧
        ∀R x y ys.
          insertaux R x (y::ys) =
          if R x y then x::y::ys else y::insertaux R x ys
   
   [insertionsort_def]  Definition
      
      ⊢ (∀R. insertionsort R [] = []) ∧
        ∀R x xs.
          insertionsort R (x::xs) = insertaux R x (insertionsort R xs)
   
   [mergesort_def']  Definition
      
      ⊢ ∀R xs. mergesort R xs = mergeall R (MAP (λx. [x]) xs)
   
   [naturalaux_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1 x2.
          asc x x0 x1 x2 = naturalaux_def_UNION (INL (x,x0,x1,x2))
   
   [naturalaux_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0. runs x x0 = naturalaux_def_UNION (INR (INL (x,x0)))
   
   [naturalaux_def_UNION_extract2]  Definition
      
      ⊢ ∀x x0 x1 x2.
          desc x x0 x1 x2 = naturalaux_def_UNION (INR (INR (x,x0,x1,x2)))
   
   [naturalaux_def_UNION_primitive]  Definition
      
      ⊢ naturalaux_def_UNION =
        WFREC
          (@R'.
             WF R' ∧
             (∀bs as b a R.
                ¬R a b ⇒ R' (INL (R,b,as ∘ CONS a,bs)) (INL (R,a,as,b::bs))) ∧
             (∀as bs b a R.
                ¬¬R a b ⇒ R' (INR (INL (R,b::bs))) (INL (R,a,as,b::bs))) ∧
             (∀xs b a R.
                R a b ⇒
                R' (INR (INR (R,b,[a],xs))) (INR (INL (R,a::b::xs)))) ∧
             (∀xs b a R.
                ¬R a b ⇒ R' (INL (R,b,CONS a,xs)) (INR (INL (R,a::b::xs)))) ∧
             (∀as bs b a R.
                ¬R a b ⇒
                R' (INR (INL (R,b::bs))) (INR (INR (R,a,as,b::bs)))) ∧
             ∀bs as b a R.
               R a b ⇒
               R' (INR (INR (R,b,a::as,bs))) (INR (INR (R,a,as,b::bs))))
          (λnaturalaux_def_UNION a'.
               case a' of
                 INL (R,a,as,[]) => I [as [a]]
               | INL (R,a,as,b::bs) =>
                 I
                   (if (¬R a b) then
                      naturalaux_def_UNION (INL (R,b,as ∘ CONS a,bs))
                    else as [a]::naturalaux_def_UNION (INR (INL (R,b::bs))))
               | INR (INL (R',[])) => I []
               | INR (INL (R',[x])) => I [[x]]
               | INR (INL (R',x::b'::xs)) =>
                 I
                   (if R' x b' then
                      naturalaux_def_UNION (INR (INR (R',b',[x],xs)))
                    else naturalaux_def_UNION (INL (R',b',CONS x,xs)))
               | INR (INR (R'',a'',as',[])) => I [a''::as']
               | INR (INR (R'',a'',as',b''::bs')) =>
                 I
                   (if R'' a'' b'' then
                      naturalaux_def_UNION
                        (INR (INR (R'',b'',a''::as',bs')))
                    else
                      (a''::as')::
                        naturalaux_def_UNION (INR (INL (R'',b''::bs')))))
   
   [naturalmerge_def]  Definition
      
      ⊢ ∀R xs. naturalmerge R xs = mergeall R (runs R xs)
   
   [LENGTH_DIV_TWO_LT]  Theorem
      
      ⊢ LENGTH l ≥ 2 ⇒ LENGTH l DIV 2 < LENGTH l
   
   [LENGTH_insertaux]  Theorem
      
      ⊢ LENGTH (insertaux R h l) = SUC (LENGTH l)
   
   [LENGTH_insertionsort]  Theorem
      
      ⊢ LENGTH (insertionsort R l) = LENGTH l
   
   [LENGTH_mergeaux]  Theorem
      
      ⊢ ∀R l. LENGTH (mergeadj R l) < SUC (LENGTH l)
   
   [LEQ_TWO_DIV_LEQ_ZERO]  Theorem
      
      ⊢ ∀n. n ≥ 2 ⇒ n DIV 2 > 0
   
   [MEM_insertaux]  Theorem
      
      ⊢ MEM x (insertaux R h l) ⇔ MEM x [h] ∨ MEM x l
   
   [MEM_insertionsort]  Theorem
      
      ⊢ ∀R L x. MEM x (insertionsort R L) ⇔ MEM x L
   
   [MEM_insertionsort']  Theorem
      
      ⊢ ∀R L x. MEM x (insertionsort R L) ⇔ MEM x L
   
   [mergeadj_def]  Theorem
      
      ⊢ (∀R. mergeadj R [] = []) ∧ (∀xs R. mergeadj R [xs] = [xs]) ∧
        ∀zs y x R. mergeadj R (x::y::zs) = mergeaux R x y::mergeadj R zs
   
   [mergeadj_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧ (∀R xs. P R [xs]) ∧
            (∀R x y zs. P R zs ⇒ P R (x::y::zs)) ⇒
            ∀v v1. P v v1
   
   [mergeall_def]  Theorem
      
      ⊢ (∀R. mergeall R [] = []) ∧ (∀xs R. mergeall R [xs] = xs) ∧
        ∀v7 v6 v2 R.
          mergeall R (v2::v6::v7) = mergeall R (mergeadj R (v2::v6::v7))
   
   [mergeall_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧ (∀R xs. P R [xs]) ∧
            (∀R v2 v6 v7. P R (mergeadj R (v2::v6::v7)) ⇒ P R (v2::v6::v7)) ⇒
            ∀v v1. P v v1
   
   [mergeaux_def]  Theorem
      
      ⊢ (∀ys R. mergeaux R [] ys = ys) ∧
        (∀v5 v4 R. mergeaux R (v4::v5) [] = v4::v5) ∧
        ∀ys y xs x R.
          mergeaux R (x::xs) (y::ys) =
          if R x y then x::mergeaux R xs (y::ys)
          else y::mergeaux R (x::xs) ys
   
   [mergeaux_ind]  Theorem
      
      ⊢ ∀P. (∀R ys. P R [] ys) ∧ (∀R v4 v5. P R (v4::v5) []) ∧
            (∀R x xs y ys.
               (¬R x y ⇒ P R (x::xs) ys) ∧ (R x y ⇒ P R xs (y::ys)) ⇒
               P R (x::xs) (y::ys)) ⇒
            ∀v v1 v2. P v v1 v2
   
   [mergesort_ind]  Theorem
      
      ⊢ ∀P. (∀R xs.
               (∀n. n = LENGTH xs ∧ ¬(n ≤ 1) ⇒ P R (DROP (n DIV 2) xs)) ∧
               (∀n. n = LENGTH xs ∧ ¬(n ≤ 1) ⇒ P R (TAKE (n DIV 2) xs)) ⇒
               P R xs) ⇒
            ∀v v1. P v v1
   
   [naturalaux_def]  Theorem
      
      ⊢ (∀as a R. asc R a as [] = [as [a]]) ∧
        (∀bs b as a R.
           asc R a as (b::bs) =
           if ¬R a b then asc R b (as ∘ CONS a) bs
           else as [a]::runs R (b::bs)) ∧ (∀R. runs R [] = []) ∧
        (∀x R. runs R [x] = [[x]]) ∧
        (∀xs b a R.
           runs R (a::b::xs) =
           if R a b then desc R b [a] xs else asc R b (CONS a) xs) ∧
        (∀as a R. desc R a as [] = [a::as]) ∧
        ∀bs b as a R.
          desc R a as (b::bs) =
          if R a b then desc R b (a::as) bs else (a::as)::runs R (b::bs)
   
   [naturalaux_ind]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀R a as. P0 R a as []) ∧
          (∀R a as b bs.
             (¬¬R a b ⇒ P1 R (b::bs)) ∧ (¬R a b ⇒ P0 R b (as ∘ CONS a) bs) ⇒
             P0 R a as (b::bs)) ∧ (∀R. P1 R []) ∧ (∀R x. P1 R [x]) ∧
          (∀R a b xs.
             (¬R a b ⇒ P0 R b (CONS a) xs) ∧ (R a b ⇒ P2 R b [a] xs) ⇒
             P1 R (a::b::xs)) ∧ (∀R a as. P2 R a as []) ∧
          (∀R a as b bs.
             (¬R a b ⇒ P1 R (b::bs)) ∧ (R a b ⇒ P2 R b (a::as) bs) ⇒
             P2 R a as (b::bs)) ⇒
          (∀v0 v1 v2 v3. P0 v0 v1 v2 v3) ∧ (∀v0 v1. P1 v0 v1) ∧
          ∀v0 v1 v2 v3. P2 v0 v1 v2 v3
   
   [quicksort_def]  Theorem
      
      ⊢ (∀R. quicksort R [] = []) ∧
        ∀xs x R.
          quicksort R (x::xs) =
          quicksort R (FILTER (λy. R y x) xs) ⧺ [x] ⧺
          quicksort R (FILTER (λy. ¬R y x) xs)
   
   [quicksort_ind]  Theorem
      
      ⊢ ∀P. (∀R. P R []) ∧
            (∀R x xs.
               P R (FILTER (λy. ¬R y x) xs) ∧ P R (FILTER (λy. R y x) xs) ⇒
               P R (x::xs)) ⇒
            ∀v v1. P v v1
   
   
*)
end
