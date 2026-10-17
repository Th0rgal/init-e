import InitECandidate.Runtime.HashTableReadySetAllPlansCeiling
import InitECandidate.Runtime.HashTableReadyGlobals
import InitECandidate.Runtime.PanSequenceReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original journal-set finish is bounded across successful and rejected growth. -/
theorem HashTableReady.jset_finish_supported_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value count : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56)
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityLarge : 1 < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state journalSetFinish32).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state journalSetFinish32).2.clock +
        2 ^ 72 ∧
      (evaluateHOLFiniteState state journalSetFinish32).2.clock ≤ state.clock := by
  let incremented := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count + 1))) state
  have nextReady := ready.after_global state keyLength table pointer keys stride capacity used values order orderPos items bits
    (ofString "journal_n") (.val (.word (count + 1))) (by decide)
  have arguments : evalListHOLFinite incremented (h := fun address => Classical.propDecidable (incremented.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [incremented,setGlobalHOLFinite,evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k,v]
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set")
    [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have u := ready.live.arrays.usedBefore
    have o := ready.live.arrays.orderBefore
    have e := ready.live.arrays.endBound
    omega
  have bounded := nextReady.set_call_supported_all_plans_ceiling incremented keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
    strideBound ready.live.frontier.aligned ready.live.frontier.bounded capacityBound ticks ready.live.frontier.heap domain
    (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value")) arguments
    capacityLarge keyAligned sourceWordDomain sourceByteDomain
  have suffix := evaluate_sequence_return_zero incremented call
  have run : evaluateHOLFiniteState state journalSetFinish32 = evaluateHOLFiniteState incremented (.seq call (.return (.const 0))) :=
    evaluate_seq_none (evaluate_journal_increment32 state count countGlobal) rfl
  rw [run]
  refine ⟨suffix.2,?_,?_⟩ <;> rw [suffix.1]
  · exact bounded.1
  · exact bounded.2

#print axioms HashTableReady.jset_finish_supported_bounded
end InitECandidate.Runtime
