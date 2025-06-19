structure quicksortCorrectnessTheory :> quicksortCorrectnessTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading quicksortCorrectnessTheory ... "
    else ()
  
  open Type Term Thm
  local open containerTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "quicksortCorrectness",
        path =
            holpathdb.subst_pathvars "/home/etranger/GitScripts/Dev/Sorting-in-HOL4/quicksortCorrectnessTheory.dat"
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  
  fun op QUICKSORT_ind _ = ()
  val op QUICKSORT_ind = TDB.find "QUICKSORT_ind"
  fun op QUICKSORT_def _ = ()
  val op QUICKSORT_def = TDB.find "QUICKSORT_def"
  fun op MEM_QUICKSORT_lemma _ = ()
  val op MEM_QUICKSORT_lemma = TDB.find "MEM_QUICKSORT_lemma"
  fun op CORRECTNESS_SORTED_QUICKSORT_thm _ = ()
  val op CORRECTNESS_SORTED_QUICKSORT_thm = TDB.find
    "CORRECTNESS_SORTED_QUICKSORT_thm"
  fun op CORRECTNESS_MSET_QUICKSORT_thm _ = ()
  val op CORRECTNESS_MSET_QUICKSORT_thm = TDB.find
    "CORRECTNESS_MSET_QUICKSORT_thm"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "quicksortCorrectness"

end
