import InitECandidate.Runtime.HashTableReady
import InitECandidate.Runtime.HashTableReadyGlobals32
import InitECandidate.Runtime.JournalSetSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A non-allocator global update preserves the complete table state. -/
theorem HashTableReady.after_global {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (name : MlS) (value : ValueHOL 64) (different : name ≠ ofString "heap_ptr") :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer
      (setGlobalHOLFinite name value state) := by
  have heap : (setGlobalHOLFinite name value state).globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using ready.live.frontier.heap
  exact ⟨⟨ready.live.arrays.after_read state _ keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
    ready.live.entries.after_memory state _ order capacity items rfl,
    ⟨heap,ready.live.frontier.allocated,ready.live.frontier.bounded,ready.live.frontier.aligned⟩⟩,
    ready.valuesWord.after_read state _ used values capacity rfl rfl rfl,
    ready.reverse.after_read state _ used orderPos capacity items rfl rfl rfl,
    ready.linked.after_read state _ used order orderPos capacity items rfl rfl rfl,ready.ordering⟩

/-- The journal counter increment executes without consuming source clock and
retains the mixed table state. -/
theorem HashTableReady.journal_increment {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items count : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    ∃ post, evaluateHOLFiniteState state
      (.assign .global (ofString "journal_n") (.op .add [.var .global (ofString "journal_n"),.const 1])) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.clock = state.clock ∧ post.locals = state.locals ∧ post.memory = state.memory ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  refine ⟨_,evaluate_journal_increment32 state count countGlobal,
    ready.after_global state keyLength table pointer keys stride capacity used values order orderPos items bits
      (ofString "journal_n") (.val (.word (count + 1))) (by decide),?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms HashTableReady.after_global
#print axioms HashTableReady.journal_increment
end InitECandidate.Runtime
