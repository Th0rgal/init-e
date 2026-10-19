import InitECandidate.Runtime.NodedbBodyReturnedFrame
import InitECandidate.Runtime.NodedbSuffixBound
/-!
The returned frame of the real `nodedb_build` suffix.

`nodedbAt 3` declares the loop index, runs the original insertion loop and
returns the caller's `t`.  For an actual returned run this module shows that the
loop cannot have returned directly (the original loop has no direct return), so
the suffix left the loop normally; the returned value is then the table pointer
and the loop's whole returned frame is available: the final loop invariant, the
typed, aligned and bounded heap frontier, the retained mapped addresses and the
protected-word memory frame.  The capacity and constructor facts are root's; the
`NodedbLoopConfig`, its geometry and the initial invariant are supplied by
`nodedb_constructor_loop_entry`.  Nothing about the callees and nothing about
post-loop memory is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Either the first program of a sequence completed normally, and the tail
produced the outcome from its final state, or the first program produced the
outcome itself. -/
theorem seq_outcome_parts {F : Type} (s : PanSemStateFiniteExact 64 F) (first tail : ProgHOL 64)
    (r : PanSemResultExact 64) (outcome : (evaluateHOLFiniteState s (.seq first tail)).1 = some r) :
    ((evaluateHOLFiniteState s first).1 = none ∧
        (evaluateHOLFiniteState (evaluateHOLFiniteState s first).2 tail).1 = some r) ∨
      (evaluateHOLFiniteState s first).1 = some r := by
  rw [evaluateHOLFiniteState_seq_line780] at outcome
  cases run : evaluateHOLFiniteState s first with
  | mk result middle =>
    rw [run] at outcome
    dsimp only at outcome
    cases result with
    | none => exact Or.inl ⟨rfl,outcome⟩
    | some result => exact Or.inr outcome

/-- The final state of a sequence whose first program completed normally is the
final state of the tail run from that state. -/
theorem seq_state_parts {F : Type} (s : PanSemStateFiniteExact 64 F) (first tail : ProgHOL 64)
    (normal : (evaluateHOLFiniteState s first).1 = none) :
    (evaluateHOLFiniteState s (.seq first tail)).2 =
      (evaluateHOLFiniteState (evaluateHOLFiniteState s first).2 tail).2 := by
  cases run : evaluateHOLFiniteState s first with
  | mk result middle =>
    rw [run] at normal
    dsimp only at normal
    subst normal
    rw [evaluateHOLFiniteState_seq_line780, run]

/-- The declared-index suffix: a returned run from the loop entry state returns
the table pointer, leaves the loop normally, and retains the loop returned
frame. -/
theorem nodedb_suffix_tail_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (c : NodedbLoopConfig) (g : NodedbLoopGeometry c) (heap : BitVec 64)
    (entry : NodedbLoopInv c 0 0 heap s)
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s (.seq nodedbInsertionLoop (.return (.var .local (ofString "t")))) =
      (some (.returned value),post)) :
    value = .val (.word c.table) ∧
      ∃ middle : PanSemStateFiniteExact 64 F, ∃ index nextCount nextHeap : BitVec 64,
        index = c.total ∧
        evaluateHOLFiniteState s nodedbInsertionLoop = (none,middle) ∧
        NodedbLoopInv c index nextCount nextHeap middle ∧
        post = emptyLocalsHOLFinite middle ∧
        post.memaddrs = s.memaddrs ∧
        (∀ w : BitVec 64, NodedbProtected c w → post.memory w = s.memory w) ∧
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
        nextHeap.toNat % 8 = 0 ∧ c.table.toNat + 72 ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧
        post.globals.lookup (ofString "keccak_st") = some (.val (.word c.pointer)) ∧
        post.globals.lookup (ofString "keccak_pad") = some (.val (.word c.pad)) ∧
        post.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word c.output)) := by
  have noReturn : ∀ v : ValueHOL 64,
      (evaluateHOLFiniteState s nodedbInsertionLoop).1 ≠ some (.returned v) :=
    fun v => evaluate_noDirectReturnWhile nodedbInsertionLoop (by decide) s v
  have parts := seq_outcome_parts s nodedbInsertionLoop (.return (.var .local (ofString "t")))
    (.returned value) (Prod.mk.inj run).1
  rcases parts with ⟨loopNormal, tailOutcome⟩ | direct
  · have loopRun : evaluateHOLFiniteState s nodedbInsertionLoop =
        (none,(evaluateHOLFiniteState s nodedbInsertionLoop).2) := Prod.ext loopNormal rfl
    have summary := nodedb_insertion_loop_normal_summary c g s (evaluateHOLFiniteState s nodedbInsertionLoop).2
      0 heap entry budget loopRun
    obtain ⟨index,nextCount,nextHeap,indexTotal,midInv,domainEq,wordFrame⟩ := summary
    have tailRun : evaluateHOLFiniteState (evaluateHOLFiniteState s nodedbInsertionLoop).2
        (.return (.var .local (ofString "t"))) =
        (some (.returned (.val (.word c.table))),
          emptyLocalsHOLFinite (evaluateHOLFiniteState s nodedbInsertionLoop).2) := by
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact,midInv.tableLocal]
      have small : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
          (evaluateHOLFiniteState s nodedbInsertionLoop).2.structs
          (shapeOfHOLExact (.val (.word c.table))) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos small]
    have postEq : (evaluateHOLFiniteState s
        (.seq nodedbInsertionLoop (.return (.var .local (ofString "t"))))).2 = post := (Prod.mk.inj run).2
    have stateEq := seq_state_parts s nodedbInsertionLoop (.return (.var .local (ofString "t"))) loopNormal
    have postForm : post = emptyLocalsHOLFinite (evaluateHOLFiniteState s nodedbInsertionLoop).2 := by
      rw [← postEq, stateEq, tailRun]
    have valueEq : value = .val (.word c.table) := by
      rw [tailRun] at tailOutcome
      exact (PanSemResultExact.returned.inj (Option.some.inj tailOutcome)).symm
    subst postForm
    refine ⟨valueEq,_,index,nextCount,nextHeap,indexTotal,loopRun,midInv,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp only [emptyLocalsHOLFinite]; exact domainEq
    · intro w kept
      simp only [emptyLocalsHOLFinite]
      exact wordFrame w kept
    · simp only [emptyLocalsHOLFinite]; exact midInv.heapGlobal
    · exact midInv.heapAligned
    · exact midInv.headerBelow
    · exact midInv.heapInside
    · simp only [emptyLocalsHOLFinite]; exact midInv.stateGlobal
    · simp only [emptyLocalsHOLFinite]; exact midInv.padGlobal
    · simp only [emptyLocalsHOLFinite]; exact midInv.outputGlobal
  · exact absurd direct (noReturn value)

/-- A word-constant declaration only restores the declared local on the way out:
its outcome, clock, memory, globals, mapped addresses and code are those of its
body. -/
theorem decConst_parts {F : Type} (s post : PanSemStateFiniteExact 64 F) (name : MlS)
    (k : BitVec 64) (body : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.dec name .one (.const k) body) = (some (.returned value),post)) :
    ∃ inner : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word k)) s) body =
        (some (.returned value),inner) ∧
      post.clock = inner.clock ∧ post.memory = inner.memory ∧ post.globals = inner.globals ∧
      post.memaddrs = inner.memaddrs ∧ post.code = inner.code := by
  rw [evaluateHOLFiniteState_dec_total] at run
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true] at run
  cases innerRun : evaluateHOLFiniteState (setVarHOLFinite name (.val (.word k)) s) body with
  | mk result inner =>
    rw [innerRun] at run
    dsimp only at run
    obtain ⟨outcomeEq, stateEq⟩ := Prod.mk.inj run
    have innerValue : (result,inner) = (some (.returned value),inner) := by
      rw [outcomeEq]
    exact ⟨inner, innerValue, by rw [← stateEq], by rw [← stateEq], by rw [← stateEq],
      by rw [← stateEq], by rw [← stateEq]⟩

/-- An actual returned run of the original suffix, index declaration included,
returns the table pointer, leaves the insertion loop normally and retains the
loop returned frame in the returned state. -/
theorem nodedb_suffix_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (c : NodedbLoopConfig) (g : NodedbLoopGeometry c) (heap : BitVec 64)
    (entry : NodedbLoopInv c 0 0 heap (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s))
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s (nodedbAt 3) = (some (.returned value),post)) :
    value = .val (.word c.table) ∧
      ∃ middle : PanSemStateFiniteExact 64 F, ∃ index nextCount nextHeap : BitVec 64,
        index = c.total ∧
        evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s)
          nodedbInsertionLoop = (none,middle) ∧
        NodedbLoopInv c index nextCount nextHeap middle ∧
        post.clock = middle.clock ∧ post.memory = middle.memory ∧ post.globals = middle.globals ∧
        post.memaddrs = middle.memaddrs ∧ post.code = middle.code ∧
        post.memaddrs = s.memaddrs ∧
        (∀ w : BitVec 64, NodedbProtected c w → post.memory w = s.memory w) ∧
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
        nextHeap.toNat % 8 = 0 ∧ c.table.toNat + 72 ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧
        post.globals.lookup (ofString "keccak_st") = some (.val (.word c.pointer)) ∧
        post.globals.lookup (ofString "keccak_pad") = some (.val (.word c.pad)) ∧
        post.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word c.output)) := by
  have declared := run
  rw [source_nodedb_insertion] at declared
  obtain ⟨inner, innerRun, clockEq, memoryEq, globalsEq, domainEq, codeEq⟩ :=
    decConst_parts s post (ofString "i") (0#64)
      (.seq nodedbInsertionLoop (.return (.var .local (ofString "t")))) value declared
  obtain ⟨valueEq, middle, index, nextCount, nextHeap, indexTotal, loopRun, midInv, postForm,
    innerDomain, wordFrame, heapGlobal, heapAligned, headerBelow, heapInside, stateGlobal, padGlobal,
    outputGlobal⟩ :=
    nodedb_suffix_tail_returned_frame (setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) inner
      value c g heap entry (by exact budget) innerRun
  refine ⟨valueEq,middle,index,nextCount,nextHeap,indexTotal,loopRun,midInv,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    ?_,?_,?_⟩
  · rw [clockEq, postForm]; rfl
  · rw [memoryEq, postForm]; rfl
  · rw [globalsEq, postForm]; rfl
  · rw [domainEq, postForm]; rfl
  · rw [codeEq, postForm]; rfl
  · exact domainEq.trans innerDomain
  · intro w kept
    exact (congrFun memoryEq w).trans (wordFrame w kept)
  · rw [globalsEq]
    simpa only [postForm,emptyLocalsHOLFinite] using heapGlobal
  · exact heapAligned
  · exact headerBelow
  · exact heapInside
  · rw [globalsEq]
    simpa only [postForm,emptyLocalsHOLFinite] using stateGlobal
  · rw [globalsEq]
    simpa only [postForm,emptyLocalsHOLFinite] using padGlobal
  · rw [globalsEq]
    simpa only [postForm,emptyLocalsHOLFinite] using outputGlobal

#print axioms seq_outcome_parts
#print axioms seq_state_parts
#print axioms nodedb_suffix_tail_returned_frame
#print axioms decConst_parts
#print axioms nodedb_suffix_returned_frame
end InitECandidate.Runtime
