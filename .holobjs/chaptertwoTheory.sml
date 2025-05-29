structure chaptertwoTheory :> chaptertwoTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading chaptertwoTheory ... "
    else ()
  
  open Type Term Thm
  local open indexedListsTheory patternMatchesTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "chaptertwo",
        path =
            holpathdb.subst_pathvars "/home/etranger/GitScripts/Dev/Sorting-in-HOL4/chaptertwoTheory.dat"
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  
  fun op quicksort_ind _ = ()
  val op quicksort_ind = TDB.find "quicksort_ind"
  fun op quicksort_def _ = ()
  val op quicksort_def = TDB.find "quicksort_def"
  fun op naturalmerge_def _ = ()
  val op naturalmerge_def = TDB.find "naturalmerge_def"
  fun op naturalaux_ind _ = ()
  val op naturalaux_ind = TDB.find "naturalaux_ind"
  fun op naturalaux_def_UNION_primitive _ = ()
  val op naturalaux_def_UNION_primitive = TDB.find
    "naturalaux_def_UNION_primitive"
  fun op naturalaux_def_UNION_extract2 _ = ()
  val op naturalaux_def_UNION_extract2 = TDB.find
    "naturalaux_def_UNION_extract2"
  fun op naturalaux_def_UNION_extract1 _ = ()
  val op naturalaux_def_UNION_extract1 = TDB.find
    "naturalaux_def_UNION_extract1"
  fun op naturalaux_def_UNION_extract0 _ = ()
  val op naturalaux_def_UNION_extract0 = TDB.find
    "naturalaux_def_UNION_extract0"
  fun op naturalaux_def _ = ()
  val op naturalaux_def = TDB.find "naturalaux_def"
  fun op mergesort_ind _ = ()
  val op mergesort_ind = TDB.find "mergesort_ind"
  fun op mergesort_def' _ = ()
  val op mergesort_def' = TDB.find "mergesort_def'"
  fun op mergeaux_ind _ = () val op mergeaux_ind = TDB.find "mergeaux_ind"
  fun op mergeaux_def _ = () val op mergeaux_def = TDB.find "mergeaux_def"
  fun op mergeall_ind _ = () val op mergeall_ind = TDB.find "mergeall_ind"
  fun op mergeall_def _ = () val op mergeall_def = TDB.find "mergeall_def"
  fun op mergeadj_ind _ = () val op mergeadj_ind = TDB.find "mergeadj_ind"
  fun op mergeadj_def _ = () val op mergeadj_def = TDB.find "mergeadj_def"
  fun op insertionsort_def _ = ()
  val op insertionsort_def = TDB.find "insertionsort_def"
  fun op insertaux_def _ = ()
  val op insertaux_def = TDB.find "insertaux_def"
  fun op MEM_insertionsort' _ = ()
  val op MEM_insertionsort' = TDB.find "MEM_insertionsort'"
  fun op MEM_insertionsort _ = ()
  val op MEM_insertionsort = TDB.find "MEM_insertionsort"
  fun op MEM_insertaux _ = ()
  val op MEM_insertaux = TDB.find "MEM_insertaux"
  fun op LEQ_TWO_DIV_LEQ_ZERO _ = ()
  val op LEQ_TWO_DIV_LEQ_ZERO = TDB.find "LEQ_TWO_DIV_LEQ_ZERO"
  fun op LENGTH_mergeaux _ = ()
  val op LENGTH_mergeaux = TDB.find "LENGTH_mergeaux"
  fun op LENGTH_insertionsort _ = ()
  val op LENGTH_insertionsort = TDB.find "LENGTH_insertionsort"
  fun op LENGTH_insertaux _ = ()
  val op LENGTH_insertaux = TDB.find "LENGTH_insertaux"
  fun op LENGTH_DIV_TWO_LT _ = ()
  val op LENGTH_DIV_TWO_LT = TDB.find "LENGTH_DIV_TWO_LT"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "chaptertwo"

val chaptertwo_grammars = valOf (Parse.grammarDB {thyname = "chaptertwo"})
end
