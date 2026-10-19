import InitECandidate.Runtime.NodedbSuffixReturnedFrame
/-!
The actual returned frame of an empty node-database build.

When the decoded entry count is zero the original insertion loop is entered with
`i = 0` and `n = 0`, so its condition is false, it returns immediately and
writes nothing.  Unlike the general suffix frame this needs no protected-word
window at all: the whole memory, the mapped addresses, the globals, the clock
and the code of the returned state are exactly those of the loop entry state,
with no budget premise.  This is the `count = 0` case where the general window
premise (`array + count * 16 ≤ entry frontier`) is vacuous for the address range
but still needed syntactically.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- From the zero-count loop entry the original insertion loop exits at once and
leaves the state untouched. -/
theorem nodedb_insertion_loop_empty {F : Type} (c : NodedbLoopConfig)
    (s : PanSemStateFiniteExact 64 F) (heap : BitVec 64)
    (empty : c.total = 0) (valid : NodedbLoopInv c 0 0 heap s) :
    evaluateHOLFiniteState s nodedbInsertionLoop = (none,s) := by
  rw [nodedbInsertionLoop,evaluateHOLFiniteState_while_total]
  rw [eval_nodedb_loop_condition s 0 c.total valid.indexLocal valid.totalLocal]
  simp [empty]

/-- An actual returned run of the original suffix with a zero entry count returns
the table pointer and leaves the whole state untouched apart from the locals of
the finished call. -/
theorem nodedb_empty_suffix_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (c : NodedbLoopConfig) (heap : BitVec 64) (empty : c.total = 0)
    (entry : NodedbLoopInv c 0 0 heap s)
    (run : evaluateHOLFiniteState s (nodedbAt 3) = (some (.returned value),post)) :
    value = .val (.word c.table) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)
        nodedbInsertionLoop = (none,setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) ∧
      post.clock = s.clock ∧ post.memory = s.memory ∧ post.globals = s.globals ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      heap.toNat % 8 = 0 ∧ heap.toNat ≤ 33806089496 ∧
      post.globals.lookup (ofString "keccak_st") = some (.val (.word c.pointer)) ∧
      post.globals.lookup (ofString "keccak_pad") = some (.val (.word c.pad)) ∧
      post.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word c.output)) := by
  have declared := run
  rw [source_nodedb_insertion] at declared
  obtain ⟨inner, innerRun, clockEq, memoryEq, globalsEq, domainEq, codeEq⟩ :=
    decConst_parts s post (ofString "i") (0#64)
      (.seq nodedbInsertionLoop (.return (.var .local (ofString "t")))) value declared
  have entryStarted : NodedbLoopInv c 0 0 heap
      (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) :=
    { entry with
      indexLocal := by
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      totalLocal := by
        simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
          using entry.totalLocal
      arrayLocal := by
        simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
          using entry.arrayLocal
      tableLocal := by
        simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
          using entry.tableLocal
      tableInv := entry.tableInv.transfer rfl rfl rfl rfl
      ordered := entry.ordered.transfer rfl rfl rfl
      arena := by
        intro a h1 h2 h3
        exact entry.arena a h1 h2 h3
      slices := by
        intro j inside
        exact entry.slices j inside }
  have loopEmpty := nodedb_insertion_loop_empty c
    (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) heap empty entryStarted
  have tailRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)
      (.return (.var .local (ofString "t"))) =
      (some (.returned (.val (.word c.table))),
        emptyLocalsHOLFinite (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)) := by
    rw [evaluateHOLFiniteState_return]
    simp only [evalHOLExact,entryStarted.tableLocal]
    have small : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
        (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s).structs
        (shapeOfHOLExact (.val (.word c.table))) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [if_pos small]
  have parts := seq_outcome_parts (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)
    nodedbInsertionLoop (.return (.var .local (ofString "t"))) (.returned value)
    (Prod.mk.inj innerRun).1
  rcases parts with ⟨loopNormal, tailOutcome⟩ | direct
  · have stateEq := seq_state_parts (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)
      nodedbInsertionLoop (.return (.var .local (ofString "t"))) loopNormal
    rw [loopEmpty] at stateEq tailOutcome
    dsimp only at stateEq
    have seqPost : (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)
        (.seq nodedbInsertionLoop (.return (.var .local (ofString "t"))))).2 = inner :=
      (Prod.mk.inj innerRun).2
    have innerForm : inner = emptyLocalsHOLFinite
        (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) := by
      rw [← seqPost, stateEq, tailRun]
    have valueEq : value = .val (.word c.table) := by
      rw [tailRun] at tailOutcome
      exact (PanSemResultExact.returned.inj (Option.some.inj tailOutcome)).symm
    refine ⟨valueEq,loopEmpty,?_,?_,?_,?_,?_,?_,entry.heapAligned,entry.heapInside,?_,?_,?_⟩
    · rw [clockEq, innerForm]; rfl
    · rw [memoryEq, innerForm]; rfl
    · rw [globalsEq, innerForm]; rfl
    · rw [domainEq, innerForm]; rfl
    · rw [codeEq, innerForm]; rfl
    · rw [globalsEq, innerForm]
      simpa only [emptyLocalsHOLFinite,setVarHOLFinite] using entry.heapGlobal
    · rw [globalsEq, innerForm]
      simpa only [emptyLocalsHOLFinite,setVarHOLFinite] using entry.stateGlobal
    · rw [globalsEq, innerForm]
      simpa only [emptyLocalsHOLFinite,setVarHOLFinite] using entry.padGlobal
    · rw [globalsEq, innerForm]
      simpa only [emptyLocalsHOLFinite,setVarHOLFinite] using entry.outputGlobal
  · exact absurd direct (fun equal => by
      rw [loopEmpty] at equal
      exact absurd equal.symm (by simp))

#print axioms nodedb_insertion_loop_empty
#print axioms nodedb_empty_suffix_returned_frame
end InitECandidate.Runtime
