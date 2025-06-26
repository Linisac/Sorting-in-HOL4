structure natural_mergesortCorrectnessTheory :> natural_mergesortCorrectnessTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading natural_mergesortCorrectnessTheory ... "
    else ()
  
  open Type Term Thm
  local open containerTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "natural_mergesortCorrectness",
        path =
            holpathdb.subst_pathvars "/home/etranger/GitScripts/Dev/Sorting-in-HOL4/natural_mergesortCorrectnessTheory.dat"
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  
  fun op SORTED_NATURAL_MERGEAUXILLARY_lemma _ = ()
  val op SORTED_NATURAL_MERGEAUXILLARY_lemma = TDB.find
    "SORTED_NATURAL_MERGEAUXILLARY_lemma"
  fun op SORTED_NATURAL_MERGEALL_lemma _ = ()
  val op SORTED_NATURAL_MERGEALL_lemma = TDB.find
    "SORTED_NATURAL_MERGEALL_lemma"
  fun op SORTED_NATURAL_MERGEADJACENT_lemma _ = ()
  val op SORTED_NATURAL_MERGEADJACENT_lemma = TDB.find
    "SORTED_NATURAL_MERGEADJACENT_lemma"
  fun op NATURAL_MERGE_ASC_RUNS_DESC_ind _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC_ind = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC_ind"
  fun op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_primitive _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_primitive = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_primitive"
  fun op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract2 _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract2 = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract2"
  fun op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract1 _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract1 = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract1"
  fun op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract0 _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract0 = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC_def_UNION_extract0"
  fun op NATURAL_MERGE_ASC_RUNS_DESC_def _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC_def = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC_def"
  fun op NATURAL_MERGE_ASC_RUNS_DESC'_ind _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC'_ind = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC'_ind"
  fun op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_primitive _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_primitive = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_primitive"
  fun op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract2 _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract2 = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract2"
  fun op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract1 _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract1 = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract1"
  fun op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract0 _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract0 = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC'_def_UNION_extract0"
  fun op NATURAL_MERGE_ASC_RUNS_DESC'_def _ = ()
  val op NATURAL_MERGE_ASC_RUNS_DESC'_def = TDB.find
    "NATURAL_MERGE_ASC_RUNS_DESC'_def"
  fun op NATURAL_MERGESORT_def _ = ()
  val op NATURAL_MERGESORT_def = TDB.find "NATURAL_MERGESORT_def"
  fun op NATURAL_MERGEAUXILLARY_ind _ = ()
  val op NATURAL_MERGEAUXILLARY_ind = TDB.find "NATURAL_MERGEAUXILLARY_ind"
  fun op NATURAL_MERGEAUXILLARY_def _ = ()
  val op NATURAL_MERGEAUXILLARY_def = TDB.find "NATURAL_MERGEAUXILLARY_def"
  fun op NATURAL_MERGEALL_ind _ = ()
  val op NATURAL_MERGEALL_ind = TDB.find "NATURAL_MERGEALL_ind"
  fun op NATURAL_MERGEALL_def _ = ()
  val op NATURAL_MERGEALL_def = TDB.find "NATURAL_MERGEALL_def"
  fun op NATURAL_MERGEADJACENT_ind _ = ()
  val op NATURAL_MERGEADJACENT_ind = TDB.find "NATURAL_MERGEADJACENT_ind"
  fun op NATURAL_MERGEADJACENT_def _ = ()
  val op NATURAL_MERGEADJACENT_def = TDB.find "NATURAL_MERGEADJACENT_def"
  fun op MSET_FLAT_ASC_RUNS_DESC_lemma _ = ()
  val op MSET_FLAT_ASC_RUNS_DESC_lemma = TDB.find
    "MSET_FLAT_ASC_RUNS_DESC_lemma"
  fun op MEM_NATURAL_MERGEAUXILLARY_lemma _ = ()
  val op MEM_NATURAL_MERGEAUXILLARY_lemma = TDB.find
    "MEM_NATURAL_MERGEAUXILLARY_lemma"
  fun op FLAT_NATURAL_MERGEAUXILLARY_lemma _ = ()
  val op FLAT_NATURAL_MERGEAUXILLARY_lemma = TDB.find
    "FLAT_NATURAL_MERGEAUXILLARY_lemma"
  fun op FLAT_NATURAL_MERGEALL_lemma _ = ()
  val op FLAT_NATURAL_MERGEALL_lemma = TDB.find
    "FLAT_NATURAL_MERGEALL_lemma"
  fun op FLAT_NATURAL_MERGEADJACENT_lemma _ = ()
  val op FLAT_NATURAL_MERGEADJACENT_lemma = TDB.find
    "FLAT_NATURAL_MERGEADJACENT_lemma"
  fun op EVERY_SORTED_ASC_RUNS_DESC_lemma _ = ()
  val op EVERY_SORTED_ASC_RUNS_DESC_lemma = TDB.find
    "EVERY_SORTED_ASC_RUNS_DESC_lemma"
  fun op EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm _ = ()
  val op EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm = TDB.find
    "EQUIV_NATURAL_MERGE_ASC_RUNS_DESC_thm"
  fun op CORRECTNESS_SORTED_NATURAL_MERGESORT _ = ()
  val op CORRECTNESS_SORTED_NATURAL_MERGESORT = TDB.find
    "CORRECTNESS_SORTED_NATURAL_MERGESORT"
  fun op CORRECTNESS_MSET_NATURAL_MERGESORT _ = ()
  val op CORRECTNESS_MSET_NATURAL_MERGESORT = TDB.find
    "CORRECTNESS_MSET_NATURAL_MERGESORT"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "natural_mergesortCorrectness"

end
