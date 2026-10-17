import InitECandidate.Runtime.StateInitJournalSource
import InitECandidate.Runtime.AllocationGlobalCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateInitJournalSetup (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .global (ofString "journal_cap") (.const 524288))
    (.seq (.call (some (some (.global,ofString "journal"),none)) (ofString "alloc")
      [.panop .mul [.var .global (ofString "journal_cap"),.const 32]])
      (.seq (.assign .global (ofString "journal_n") (.const 0))
        (.seq (.assign .global (ofString "ts") (.const 0)) continuation)))

theorem stateInitJournalTail_eq_setup : stateInitJournalTail = stateInitJournalSetup (.return (.const 0)) := rfl

/-- Actual journal capacity assignment, reserved-buffer allocation and reset
reach any continuation in exactly one source clock, preserving memory. -/
theorem evaluate_stateInit_journal_setup {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldCapacity oldJournal oldCount oldTs : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacity : state.globals.lookup (ofString "journal_cap") = some (.val (.word oldCapacity)))
    (journal : state.globals.lookup (ofString "journal") = some (.val (.word oldJournal)))
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (ts : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (request : (16777216 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (finish : (allocationEnd pointer 16777216).toNat ≤ 33806089496) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state (stateInitJournalSetup continuation) = evaluateHOLFiniteState post continuation) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.locals = state.locals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))) ∧
      post.globals.lookup (ofString "journal") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (0 : BitVec 64))) ∧
      post.globals.lookup (ofString "ts") = some (.val (.word (0 : BitVec 64))) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 16777216))) ∧
      (∀ name, name ≠ ofString "journal_cap" → name ≠ ofString "journal" → name ≠ ofString "journal_n" → name ≠ ofString "ts" → name ≠ ofString "heap_ptr" →
        post.globals.lookup name = state.globals.lookup name) := by
  let capped := setGlobalHOLFinite (ofString "journal_cap") (.val (.word (524288 : BitVec 64))) state
  have capRun : evaluateHOLFiniteState state (.assign .global (ofString "journal_cap") (.const 524288)) = (none,capped) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,lookupKvarHOLExact,capacity,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,capped]
  have capFrame : ∀ name, name ≠ ofString "journal_cap" → capped.globals.lookup name = state.globals.lookup name := by
    intro name different
    simp [capped,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have arguments : evalListHOLFinite capped (h := fun address => Classical.propDecidable (capped.memaddrs address))
      [.panop .mul [.var .global (ofString "journal_cap"),.const 32]] = some [.val (.word (16777216 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capped,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,panOpHOL,valueIsWord,valueWord]
  obtain ⟨allocated,allocationRun,ticks,memory,locals,postCode,domain,endian,journalAfter,heapAfter,globals⟩ :=
    evaluate_alloc_global_call capped _ pointer 16777216 oldJournal (ofString "journal") arguments code clock
      ((capFrame (ofString "heap_ptr") (by decide)).trans heap) ((capFrame (ofString "journal") (by decide)).trans journal)
      (by decide) request finish
  let counted := setGlobalHOLFinite (ofString "journal_n") (.val (.word (0 : BitVec 64))) allocated
  let post := setGlobalHOLFinite (ofString "ts") (.val (.word (0 : BitVec 64))) counted
  have counterAfter : allocated.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)) :=
    (globals (ofString "journal_n") (by decide) (by decide)).trans ((capFrame (ofString "journal_n") (by decide)).trans counter)
  have countRun : evaluateHOLFiniteState allocated (.assign .global (ofString "journal_n") (.const 0)) = (none,counted) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,lookupKvarHOLExact,counterAfter,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,counted]
  have tsAfter : counted.globals.lookup (ofString "ts") = some (.val (.word oldTs)) := by
    have prior := (globals (ofString "ts") (by decide) (by decide)).trans ((capFrame (ofString "ts") (by decide)).trans ts)
    simpa [counted,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "journal_n" ≠ ofString "ts" from by decide] using prior
  have tsRun : evaluateHOLFiniteState counted (.assign .global (ofString "ts") (.const 0)) = (none,post) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,lookupKvarHOLExact,tsAfter,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,post]
  have resetFrame : ∀ name, name ≠ ofString "ts" → name ≠ ofString "journal_n" → post.globals.lookup name = allocated.globals.lookup name := by
    intro name notTs notCount
    simp [post,counted,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notTs,Ne.symm notCount]
  refine ⟨post,?_,ticks,memory,locals,postCode,domain,endian,?_,?_,?_,?_,?_,?_⟩
  · intro continuation
    unfold stateInitJournalSetup
    rw [evaluateHOLFiniteState_seq_line780,capRun]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,allocationRun]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,countRun]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,tsRun]
  · rw [resetFrame _ (by decide) (by decide),globals _ (by decide) (by decide)]
    simp [capped,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact (resetFrame _ (by decide) (by decide)).trans journalAfter
  · simp [post,counted,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [post,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact (resetFrame _ (by decide) (by decide)).trans heapAfter
  · intro name notCap notJournal notCount notTs notHeap
    exact (resetFrame name notTs notCount).trans ((globals name notJournal notHeap).trans (capFrame name notCap))

#print axioms evaluate_stateInit_journal_setup
#print axioms stateInitJournalTail_eq_setup
end InitECandidate.Runtime
