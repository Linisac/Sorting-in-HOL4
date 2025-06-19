structure topdown_mergesortCorrectnessTheory :> topdown_mergesortCorrectnessTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading topdown_mergesortCorrectnessTheory ... "
    else ()
  
  open Type Term Thm
  local open containerTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "topdown_mergesortCorrectness",
        path =
            holpathdb.subst_pathvars "/home/etranger/GitScripts/Dev/Sorting-in-HOL4/topdown_mergesortCorrectnessTheory.dat"
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  
  fun op TOP_DOWN_MERGESORT_ind _ = ()
  val op TOP_DOWN_MERGESORT_ind = TDB.find "TOP_DOWN_MERGESORT_ind"
  fun op TOP_DOWN_MERGESORT_def _ = ()
  val op TOP_DOWN_MERGESORT_def = TDB.find "TOP_DOWN_MERGESORT_def"
  fun op TOP_DOWN_MERGEAUXILLARY_ind _ = ()
  val op TOP_DOWN_MERGEAUXILLARY_ind = TDB.find
    "TOP_DOWN_MERGEAUXILLARY_ind"
  fun op TOP_DOWN_MERGEAUXILLARY_def _ = ()
  val op TOP_DOWN_MERGEAUXILLARY_def = TDB.find
    "TOP_DOWN_MERGEAUXILLARY_def"
  fun op SORTED_MERGEAUXILLARY_lemma _ = ()
  val op SORTED_MERGEAUXILLARY_lemma = TDB.find
    "SORTED_MERGEAUXILLARY_lemma"
  fun op MSET_MERGEAUXILLARY_lemma _ = ()
  val op MSET_MERGEAUXILLARY_lemma = TDB.find "MSET_MERGEAUXILLARY_lemma"
  fun op MEM_TOP_DOWN_MERGEAUXILLARY_lemma _ = ()
  val op MEM_TOP_DOWN_MERGEAUXILLARY_lemma = TDB.find
    "MEM_TOP_DOWN_MERGEAUXILLARY_lemma"
  fun op CORRECTNESS_SORTED_TOP_DOWN_MERGESORT_thm _ = ()
  val op CORRECTNESS_SORTED_TOP_DOWN_MERGESORT_thm = TDB.find
    "CORRECTNESS_SORTED_TOP_DOWN_MERGESORT_thm"
  fun op CORRECTNESS_MSET_TOP_DOWN_MERGESORT_thm _ = ()
  val op CORRECTNESS_MSET_TOP_DOWN_MERGESORT_thm = TDB.find
    "CORRECTNESS_MSET_TOP_DOWN_MERGESORT_thm"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "topdown_mergesortCorrectness"

end
