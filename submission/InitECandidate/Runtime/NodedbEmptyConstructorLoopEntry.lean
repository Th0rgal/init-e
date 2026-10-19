import InitECandidate.Runtime.NodedbEmptyReturnedFrame
/-!
Zero-count node-database builds, without window geometry.

Two compatible helpers for the `count = 0` case:

* `nodedb_empty_constructor_loop_entry` builds the loop config and the
  after-declaration loop invariant straight from the actual constructor
  normal-return contract (`NodedbTableReady`).  Because the entry count is zero
  the slice clause is vacuous and the table geometry is never needed: no
  `arrayEnd`/`stateEnd`/`padEnd`/`outputEnd`, no `NodedbLoopGeometry`, no
  capacity margin and no output alignment premise appear.
* `nodedb_empty_declared_suffix_returned_frame` is the empty suffix returned
  frame stated with the after-declaration invariant, i.e. the exact interface
  `nodedb_constructor_loop_entry` (and the helper above) supplies.  It returns
  the table pointer and keeps clock, memory, globals, mapped addresses and code
  of the loop entry state, so an empty build needs no protected-word window and
  no budget.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- With a zero decoded entry count the actual constructor normal-return contract
alone yields the loop config (`total = 0`, table at the entry frontier, workspace
pointers retained) and the after-declaration loop invariant.  No window geometry
and no slice premise is needed. -/
theorem nodedb_empty_constructor_loop_entry {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (pointer capacity total array statePad pad output : BitVec 64) (bits : Nat)
    (ready : NodedbTableReady s pointer capacity bits next)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (empty : total = 0)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a) :
    ∃ c : NodedbLoopConfig, c.total = 0 ∧ c.capacity = capacity ∧ c.table = pointer ∧
      c.pointer = statePad ∧ c.pad = pad ∧ c.array = array ∧ c.output = output ∧
      ∃ heap : BitVec 64, NodedbLoopInv c 0 0 heap
        (setVarHOLFinite (ofString "i") (.val (.word (0#64))) next) := by
  subst empty
  obtain ⟨tableLocal,locals,code,domain,endian,frame,rel,keys,stride,used,values,order,orderPos,inv,keysBefore,
    ordered,heap,heapGlobal,extent,heapAligned,heapInside⟩ := ready
  let c : NodedbLoopConfig :=
    ⟨statePad,pad,array,0,output,pointer,keys,stride,capacity,used,values,order,orderPos,bits⟩
  have keep (key : MlS) (different : key ≠ ofString "i") :
      (setVarHOLFinite (ofString "i") (.val (.word (0#64))) next).locals.lookup key =
        next.locals.lookup key := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨c,rfl,rfl,rfl,rfl,rfl,rfl,rfl,heap,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact ((keep _ (by decide)).trans (locals _ (by decide))).trans atTotal
  · exact ((keep _ (by decide)).trans (locals _ (by decide))).trans atArray
  · exact (keep _ (by decide)).trans tableLocal
  · exact (rel.1 _ (by decide)).trans atState
  · exact (rel.1 _ (by decide)).trans atPad
  · exact (rel.1 _ (by decide)).trans atOutput
  · exact heapGlobal
  · exact heapAligned
  · have headerKeys := inv.headerKeys
    have keysBefore' := keysBefore
    have valuesBefore := inv.valuesBefore
    have usedBefore := inv.usedBefore
    have orderBefore := inv.orderBefore
    show pointer.toNat + 72 ≤ heap.toNat
    omega
  · exact heapInside
  · simp [c]
  · simp
  · exact inv.transfer rfl rfl rfl rfl
  · exact ordered.transfer rfl rfl rfl
  · intro a h1 h2 h3
    change next.memaddrs a
    rw [domain]
    exact arena a h1 h2 h3
  · intro j inside
    exact absurd inside (by simp [c])

/-- An actual returned run of the original suffix with a zero entry count returns
the table pointer and leaves the whole state untouched apart from the locals of
the finished call. -/
theorem nodedb_empty_declared_suffix_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (c : NodedbLoopConfig) (heap : BitVec 64) (empty : c.total = 0)
    (entry : NodedbLoopInv c 0 0 heap (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s))
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
  have loopEmpty := nodedb_insertion_loop_empty c
    (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) heap empty entry
  have tailRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)
      (.return (.var .local (ofString "t"))) =
      (some (.returned (.val (.word c.table))),
        emptyLocalsHOLFinite (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)) := by
    rw [evaluateHOLFiniteState_return]
    simp only [evalHOLExact,entry.tableLocal]
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

#print axioms nodedb_empty_constructor_loop_entry
#print axioms nodedb_empty_declared_suffix_returned_frame
end InitECandidate.Runtime
