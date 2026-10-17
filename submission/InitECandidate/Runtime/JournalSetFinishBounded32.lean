import InitECandidate.Runtime.HashTableSetCallBounded32
import InitECandidate.Runtime.HashTableReadyGlobals32
import InitECandidate.Runtime.PanSequenceReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original journal-set finish is bounded across successful and rejected growth. -/
theorem HashTableReady32.jset_finish_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value count : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 3 * capacity.toNat + 2 * (capacity * 2).toNat + 45 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state journalSetFinish32).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state journalSetFinish32).2.clock +
        3 * capacity.toNat + 2 * (capacity * 2).toNat + 45 + items.toNat * ((capacity * 2).toNat + 36) ∧
      (evaluateHOLFiniteState state journalSetFinish32).2.clock ≤ state.clock := by
  let incremented := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) state
  have nextReady := ready.after_global state table pointer keys stride capacity used values order orderPos items bits
    (ofString "journal_n") (.val (.word (count + 1))) (by decide)
  have arguments : evalListHOLFinite incremented (h := fun address => Classical.propDecidable (incremented.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [incremented,setGlobalHOLFinite,evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k,v]
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set")
    [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]
  have bounded := nextReady.set_call_bounded incremented table pointer keys stride capacity used values order orderPos items key value bits
    strideBound ticks domain capacityLarge keyAligned sourceWordDomain sourceByteDomain
    (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value")) arguments
  have suffix := evaluate_sequence_return_zero incremented call
  have run : evaluateHOLFiniteState state journalSetFinish32 = evaluateHOLFiniteState incremented (.seq call (.return (.const 0))) :=
    evaluate_seq_none (evaluate_journal_increment32 state count countGlobal) rfl
  rw [run]
  refine ⟨suffix.2,?_,?_⟩ <;> rw [suffix.1]
  · exact bounded.1
  · exact bounded.2

#print axioms HashTableReady32.jset_finish_bounded
end InitECandidate.Runtime
