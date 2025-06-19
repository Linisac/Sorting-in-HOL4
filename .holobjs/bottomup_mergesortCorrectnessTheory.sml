structure bottomup_mergesortCorrectnessTheory :> bottomup_mergesortCorrectnessTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading bottomup_mergesortCorrectnessTheory ... "
    else ()
  
  open Type Term Thm
  local open containerTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "bottomup_mergesortCorrectness",
        path =
            holpathdb.subst_pathvars "/home/etranger/GitScripts/Dev/Sorting-in-HOL4/bottomup_mergesortCorrectnessTheory.dat"
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  
  fun op SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma _ = ()
  val op SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma = TDB.find
    "SORTED_BOTTOM_UP_MERGEAUXILLARY_lemma"
  fun op SORTED_BOTTOM_UP_MERGEADJACENT_lemma _ = ()
  val op SORTED_BOTTOM_UP_MERGEADJACENT_lemma = TDB.find
    "SORTED_BOTTOM_UP_MERGEADJACENT_lemma"
  fun op MSET_BOTTOM_UP_MERGEAUXILLARY_lemma _ = ()
  val op MSET_BOTTOM_UP_MERGEAUXILLARY_lemma = TDB.find
    "MSET_BOTTOM_UP_MERGEAUXILLARY_lemma"
  fun op MSET_BOTTOM_UP_MERGEALL_lemma _ = ()
  val op MSET_BOTTOM_UP_MERGEALL_lemma = TDB.find
    "MSET_BOTTOM_UP_MERGEALL_lemma"
  fun op MSET_BOTTOM_UP_MERGEADJACENT_lemma _ = ()
  val op MSET_BOTTOM_UP_MERGEADJACENT_lemma = TDB.find
    "MSET_BOTTOM_UP_MERGEADJACENT_lemma"
  fun op MEM_BOTTOM_UP_MERGEAUXILLARY_lemma _ = ()
  val op MEM_BOTTOM_UP_MERGEAUXILLARY_lemma = TDB.find
    "MEM_BOTTOM_UP_MERGEAUXILLARY_lemma"
  fun op CORRECTNESS_SORTED_BOTTOM_UP_MERGESORT_thm _ = ()
  val op CORRECTNESS_SORTED_BOTTOM_UP_MERGESORT_thm = TDB.find
    "CORRECTNESS_SORTED_BOTTOM_UP_MERGESORT_thm"
  fun op CORRECTNESS_MSET_BOTTOM_UP_MERGESORT_thm _ = ()
  val op CORRECTNESS_MSET_BOTTOM_UP_MERGESORT_thm = TDB.find
    "CORRECTNESS_MSET_BOTTOM_UP_MERGESORT_thm"
  fun op BOTTOM_UP_MERGESORT_def _ = ()
  val op BOTTOM_UP_MERGESORT_def = TDB.find "BOTTOM_UP_MERGESORT_def"
  fun op BOTTOM_UP_MERGEAUXILLARY_ind _ = ()
  val op BOTTOM_UP_MERGEAUXILLARY_ind = TDB.find
    "BOTTOM_UP_MERGEAUXILLARY_ind"
  fun op BOTTOM_UP_MERGEAUXILLARY_def _ = ()
  val op BOTTOM_UP_MERGEAUXILLARY_def = TDB.find
    "BOTTOM_UP_MERGEAUXILLARY_def"
  fun op BOTTOM_UP_MERGEALL_ind _ = ()
  val op BOTTOM_UP_MERGEALL_ind = TDB.find "BOTTOM_UP_MERGEALL_ind"
  fun op BOTTOM_UP_MERGEALL_def _ = ()
  val op BOTTOM_UP_MERGEALL_def = TDB.find "BOTTOM_UP_MERGEALL_def"
  fun op BOTTOM_UP_MERGEALL_MAP_lemma _ = ()
  val op BOTTOM_UP_MERGEALL_MAP_lemma = TDB.find
    "BOTTOM_UP_MERGEALL_MAP_lemma"
  fun op BOTTOM_UP_MERGEADJACENT_ind _ = ()
  val op BOTTOM_UP_MERGEADJACENT_ind = TDB.find
    "BOTTOM_UP_MERGEADJACENT_ind"
  fun op BOTTOM_UP_MERGEADJACENT_def _ = ()
  val op BOTTOM_UP_MERGEADJACENT_def = TDB.find
    "BOTTOM_UP_MERGEADJACENT_def"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "bottomup_mergesortCorrectness"

end
