import InitECandidate.Runtime.HashTableReady32
import InitECandidate.Runtime.JournalSetSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A non-allocator global update preserves the complete table state. -/
theorem HashTableReady32.after_global {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (name : MlS) (value : ValueHOL 64) (different : name ≠ ofString "heap_ptr") :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer
      (setGlobalHOLFinite name value state) := by
  have heap : (setGlobalHOLFinite name value state).globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using ready.live.frontier.heap
  exact ⟨⟨ready.live.arrays.after_read state _ table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
    ready.live.entries.after_memory state _ order capacity items rfl,
    ⟨heap,ready.live.frontier.allocated,ready.live.frontier.bounded,ready.live.frontier.aligned⟩⟩,
    ready.valuesWord.after_read state _ used values capacity rfl rfl rfl,
    ready.reverse.after_read state _ used orderPos capacity items rfl rfl rfl,
    ready.linked.after_read state _ used order orderPos capacity items rfl rfl rfl,ready.ordering⟩

theorem evaluate_journal_increment32 {F : Type} (state : PanSemStateFiniteExact 64 F) (count : BitVec 64)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    evaluateHOLFiniteState state
      (.assign .global (ofString "journal_n") (.op .add [.var .global (ofString "journal_n"),.const 1])) =
      (none,setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) state) := by
  rw [evaluateHOLFiniteState_assign]
  simp [evalHOLExact,evalListHOLExact,countGlobal,wordOpHOL,wordOp,valueIsWord,valueWord,
    shapeOfHOLExact,shapeEqHOL,isValidValueHOLExact,lookupKvarHOLExact,setKvarHOLFinite,setGlobalHOLFinite]

/-- The journal counter increment executes without consuming source clock and
retains the mixed table state. -/
theorem HashTableReady32.journal_increment {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items count : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    ∃ post, evaluateHOLFiniteState state
      (.assign .global (ofString "journal_n") (.op .add [.var .global (ofString "journal_n"),.const 1])) = (none,post) ∧
      HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.clock = state.clock ∧ post.locals = state.locals ∧ post.memory = state.memory ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  refine ⟨_,evaluate_journal_increment32 state count countGlobal,
    ready.after_global state table pointer keys stride capacity used values order orderPos items bits
      (ofString "journal_n") (.val (.word (count + 1))) (by decide),?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- The exact journal-set suffix composes the counter update, original set
call, and final return without additional source-clock consumption. -/
theorem evaluate_journalSetFinish32 {F : Type} (state post : PanSemStateFiniteExact 64 F) (count : BitVec 64)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (setRun : evaluateHOLFiniteState
      (setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) state)
      (.call (some (none,none)) (ofString "htab_set")
        [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) = (none,post)) :
    evaluateHOLFiniteState state journalSetFinish32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
  have returned : evaluateHOLFiniteState post (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  exact evaluate_seq_none (evaluate_journal_increment32 state count countGlobal) (evaluate_seq_none setRun returned)

#print axioms evaluate_journalSetFinish32
#print axioms HashTableReady32.after_global
#print axioms evaluate_journal_increment32
#print axioms HashTableReady32.journal_increment
end InitECandidate.Runtime
