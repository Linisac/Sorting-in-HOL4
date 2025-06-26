structure insertionsortCorrectnessTheory :> insertionsortCorrectnessTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading insertionsortCorrectnessTheory ... "
    else ()
  
  open Type Term Thm
  local open containerTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "insertionsortCorrectness",
        path =
            holpathdb.subst_pathvars "/home/etranger/GitScripts/Dev/Sorting-in-HOL4/insertionsortCorrectnessTheory.dat"
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  
  fun op SORTED_INSERTIONAUXILLARY_lemma _ = ()
  val op SORTED_INSERTIONAUXILLARY_lemma = TDB.find
    "SORTED_INSERTIONAUXILLARY_lemma"
  fun op MSET_INSERTION_AUXILLARY_lemma _ = ()
  val op MSET_INSERTION_AUXILLARY_lemma = TDB.find
    "MSET_INSERTION_AUXILLARY_lemma"
  fun op MEM_INSERTIONAUXILLARY_lemma _ = ()
  val op MEM_INSERTIONAUXILLARY_lemma = TDB.find
    "MEM_INSERTIONAUXILLARY_lemma"
  fun op INSERTION_AUXILLARY_def _ = ()
  val op INSERTION_AUXILLARY_def = TDB.find "INSERTION_AUXILLARY_def"
  fun op INSERTIONSORT_def _ = ()
  val op INSERTIONSORT_def = TDB.find "INSERTIONSORT_def"
  fun op CORRECTNNESS_MSET_INSERTSORT _ = ()
  val op CORRECTNNESS_MSET_INSERTSORT = TDB.find
    "CORRECTNNESS_MSET_INSERTSORT"
  fun op CORRECTNESS_SORTED_INSERTIONSORT_thm _ = ()
  val op CORRECTNESS_SORTED_INSERTIONSORT_thm = TDB.find
    "CORRECTNESS_SORTED_INSERTIONSORT_thm"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "insertionsortCorrectness"

end
