import InitECandidate.Runtime.StateFreshTxSequence
import InitECandidate.Runtime.RollbackWorldResetReturnFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual constructor/store sequence followed by reset and return
establishes the empty separated rollback world, under cumulative entry bounds. -/
theorem evaluate_stateFreshTx_sequence_reset_frame {F : Type} (widths : BitVec 64 → BitVec 64)
    (specs : List (Nat × Nat × Nat)) :
    ∀ (state : PanSemStateFiniteExact 64 F) (pointer ts oldValue : BitVec 64) (tables : Set (BitVec 64)) (journal snapshot oldCount : BitVec 64),
    StateFreshTxPlan widths pointer specs →
    (∀ table ∈ tables, RollbackTableReady widths table state) → RollbackPhysicalSeparated widths tables state →
    state.code = originalRuntimeCode → state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) →
    state.globals.lookup (ofString "ts") = some (.val (.word ts)) → state.locals.lookup (ofString "t") = some (.val (.word oldValue)) →
    pointer.toNat % 8 = 0 → ts.toNat + 72 ≤ pointer.toNat →
    (∀ table ∈ tables, ts.toNat + 72 ≤ table.toNat) →
    (∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) →
    pointer.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 → stateFreshTxClockBudget specs ≤ state.clock →
    state.globals.lookup (ofString "journal") = some (.val (.word journal)) →
    state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)) → journal.toNat ≤ ts.toNat + 72 →
    ∃ post, evaluateHOLFiniteState state (stateFreshTxConstructorSequence specs
      (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0)))) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) ∧
      RollbackWorld widths (stateFreshTxRegistryAfter pointer specs tables) journal snapshot 0
        (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
      RollbackPhysicalSeparated widths (stateFreshTxRegistryAfter pointer specs tables) post ∧
      state.clock ≤ post.clock + stateFreshTxClockBudget specs ∧ post.clock ≤ state.clock ∧ post.memaddrs = state.memaddrs ∧ post.code = state.code ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "journal_n" → post.globals.lookup name = state.globals.lookup name) := by
  intro state pointer ts oldValue tables journal snapshot oldCount plan family apart code heap tsGlobal tLocal aligned header headers domain space ticks journalGlobal counterGlobal journalBefore
  obtain ⟨middle,run,registry,midApart,midHeaders,_,midCode,midDomain,midEndian,midGlobals,_,cost,remaining⟩ :=
    evaluate_stateFreshTx_constructor_sequence widths specs state pointer ts oldValue tables plan family apart code heap tsGlobal tLocal
      aligned header headers domain space ticks
  obtain ⟨post,finish,world,postApart,clock,postDomain⟩ := rollback_reset_return_establishes_world middle widths
    (stateFreshTxRegistryAfter pointer specs tables) journal snapshot oldCount registry midApart
    ((midGlobals (ofString "journal_n") (by decide)).trans counterGlobal)
    ((midGlobals (ofString "journal") (by decide)).trans journalGlobal)
    (by intro table member; have afterHeader := midHeaders table member; omega)
  have frame := rollback_reset_return_frame middle oldCount ((midGlobals (ofString "journal_n") (by decide)).trans counterGlobal)
  rw [finish] at frame
  refine ⟨post,(run _).trans finish,world,postApart,by omega,by omega,postDomain.trans midDomain,frame.1.trans midCode,frame.2.1.trans midEndian,?_⟩
  intro name notHeap notCounter
  exact (frame.2.2 name notCounter).trans (midGlobals name notHeap)

#print axioms evaluate_stateFreshTx_sequence_reset_frame
end InitECandidate.Runtime
