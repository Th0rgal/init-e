import InitECandidate.Runtime.GlobalAllocationPrefix
import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.PanStoreChain
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem seq_returned_of_nonreturning_first {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {first tail : ProgHOL 64} {value : ValueHOL 64}
    (noReturn : ∀ v, (evaluateHOLFiniteState state first).1 ≠ some (.returned v))
    (run : evaluateHOLFiniteState state (.seq first tail) = (some (.returned value),post)) :
    ∃ next, evaluateHOLFiniteState state first = (none,next) ∧
      evaluateHOLFiniteState next tail = (some (.returned value),post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state first with
  | mk result next =>
    rw [firstRun] at run
    cases result with
    | none => exact ⟨next,rfl,run⟩
    | some result =>
      have forbidden := noReturn value
      rw [firstRun] at forbidden
      exact False.elim (forbidden (congrArg Prod.fst run))

/-- A literal allocator sequence may contain arbitrary intervening programs
that preserve globals and cannot themselves return from the whole sequence. -/
inductive AllocationFramedGlobals : ProgHOL 64 → List (MlS × BitVec 64) → Prop
  | finish : AllocationFramedGlobals (.return (.const 0)) []
  | framed (first : ProgHOL 64) {tail : ProgHOL 64} {entries : List (MlS × BitVec 64)}
      (frame : OriginalGlobalsFrame first)
      (noReturn : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64),
        (evaluateHOLFiniteState state first).1 ≠ some (.returned value))
      (rest : AllocationFramedGlobals tail entries) :
      AllocationFramedGlobals (.seq first tail) entries
  | allocation (name : MlS) (size : BitVec 64) {tail : ProgHOL 64} {entries : List (MlS × BitVec 64)}
      (rest : AllocationFramedGlobals tail entries) :
      AllocationFramedGlobals (globalAllocationProgram [(name,size)] tail) ((name,size) :: entries)

/-- On a returned run, allocator assignments give the exact global map.
Intervening errors are excluded by the returned execution, not by extra
memory-access or success assumptions about the framed programs. -/
theorem AllocationFramedGlobals.returned {program : ProgHOL 64} {entries : List (MlS × BitVec 64)}
    (fragment : AllocationFramedGlobals program entries)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (names : ∀ entry ∈ entries, entry.1 ≠ ofString "heap_ptr")
    (words : ∀ entry ∈ entries, ∃ word : BitVec 64, state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (entries.map Prod.snd))
    (run : evaluateHOLFiniteState state program = (some (.returned value),post)) :
    value = .val (.word 0) ∧ post.globals = globalAllocationGlobals state.globals pointer entries := by
  induction fragment generalizing state pointer with
  | finish =>
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact] at run
    obtain ⟨equal,postEq⟩ := run
    exact ⟨equal.symm,by rw [← postEq]; rfl⟩
  | framed first frame noReturn rest ih =>
    obtain ⟨middle,firstRun,restRun⟩ := seq_returned_of_nonreturning_first (noReturn state) run
    have globals := frame state code
    have metadata := evaluateHOLFiniteState_metadata state first
    rw [firstRun] at globals metadata
    obtain ⟨zero,returnedGlobals⟩ := ih middle pointer (metadata.1.trans code)
      (by rw [globals]; exact heap) names
      (by intro entry member; rw [globals]; exact words entry member) safe restRun
    exact ⟨zero,by rw [returnedGlobals,globals]⟩
  | @allocation name size tail entries rest ih =>
    have parts : size ≤ (33806089496 : BitVec 64) - pointer ∧
        (allocationEnd pointer size).toNat ≤ 33806089496 ∧
        AllocationPlanSafe (allocationEnd pointer size) (entries.map Prod.snd) := safe
    have oneSafe : AllocationPlanSafe pointer [size] := ⟨parts.1,parts.2.1,parts.2.1⟩
    have different := names (name,size) (by simp)
    obtain ⟨old,slot⟩ := words (name,size) (by simp)
    have nonzero : state.clock ≠ 0 := call_seq_returned_clock run
    obtain ⟨middle,prefixRun,_,_,_,installed,_,globals,heapNext⟩ :=
      evaluate_globalAllocation_prefix state [(name,size)] _ pointer code heap
        (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact different)
        (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨old,slot⟩)
        oneSafe (by simp; omega)
    have restNames : ∀ entry ∈ entries, entry.1 ≠ ofString "heap_ptr" := by
      intro entry member
      exact names entry (by simp [member])
    have restWords : ∀ entry ∈ entries, ∃ word : BitVec 64, middle.globals.lookup entry.1 = some (.val (.word word)) := by
      intro entry member
      by_cases same : entry.1 = name
      · refine ⟨pointer,?_⟩
        rw [globals]
        simp [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,same]
      · obtain ⟨word,original⟩ := words entry (by simp [member])
        refine ⟨word,?_⟩
        rw [globals]
        simpa [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same,
          Ne.symm (restNames entry member)] using original
    obtain ⟨zero,returnedGlobals⟩ := ih middle (allocationEnd pointer size) (installed.trans code)
      heapNext restNames restWords parts.2.2 (prefixRun.symm.trans run)
    refine ⟨zero,?_⟩
    rw [returnedGlobals,globals]
    rfl

theorem globalAllocationGlobals_heap_frontier (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) (entries : List (MlS × BitVec 64))
    (heap : globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (names : ∀ entry ∈ entries, entry.1 ≠ ofString "heap_ptr") :
    (globalAllocationGlobals globals pointer entries).lookup (ofString "heap_ptr") =
      some (.val (.word (allocationPlanEnd pointer (entries.map Prod.snd)))) := by
  induction entries generalizing globals pointer with
  | nil => exact heap
  | cons entry rest ih =>
    obtain ⟨name,size⟩ := entry
    apply ih
    · simp [HolFiniteMapExact.lookup_update,FUPDATE,names (name,size) (by simp)]
    · intro entry member
      exact names entry (by simp [member])

#print axioms globalAllocationGlobals_heap_frontier
#print axioms seq_returned_of_nonreturning_first
#print axioms AllocationFramedGlobals.returned
end InitECandidate.Runtime
