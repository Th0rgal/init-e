import InitECandidate.Runtime.JournalSetBoundedOtherSupported
import InitECandidate.Runtime.JournalSetCallOtherSupported
import InitECandidate.Runtime.PanCallBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform actual jset call bound over all journal and allocation outcomes. -/
theorem HashTableReady.jset_call_supported_bounded_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (sourceAligned : key.toNat % 8 = 0) (ticks : 2 ^ 72 + 2 * capacity.toNat + keyLength.toNat + 6 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)
    (strideBound : stride.toNat ≤ 56)
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)]) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2.clock +
      2 ^ 72 + 2 * capacity.toNat + keyLength.toNat + 6 ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have vt : ofString "value" ≠ ofString "t" := by decide
  have vk : ofString "value" ≠ ofString "key" := by decide
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vt,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vk]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryReady := ready.after_read state entry keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have entryOther := otherReady.after_read state entry otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl
  have bounded := entryReady.jset_supported_bounded_with_other entry keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value bits supported
    k sourceAligned (by change 2 ^ 72 + 2 * capacity.toNat + keyLength.toNat + 5 ≤ state.clock - 1; omega)
    wordDomain byteDomain sourceWordDomain sourceByteDomain t journalGlobal countGlobal capacityGlobal
    journalBound journalAligned journalOutside journalDomain v strideBound capacityLarge growDomain
    otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits entryOther otherJournalOutside separate beforeKeys beforeValues
  have installed : state.code.lookup (ofString "jset") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_jset,.one) := by
    rw [ready.live.arrays.code]; exact originalRuntimeCode_journalSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "jset") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_jset) table key value (by decide) (by decide) (by decide) installed
  have result := evaluate_call_body_bound state (ofString "jset") [tableArgument,keyArgument,valueArgument]
    [.val (.word table),.val (.word key),.val (.word value)] (sourceFunctionBody Guest.guestFn_jset) callee .one
    (2 ^ 72 + 2 * capacity.toNat + keyLength.toNat + 5)
    arguments lookup (by omega) (by change entry.clock ≤ (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).2.clock + (2 ^ 72 + 2 * capacity.toNat + keyLength.toNat + 5); have cost := bounded.2.1; omega) bounded.2.2
  exact ⟨by have cost := result.1; omega,result.2⟩

#print axioms HashTableReady.jset_call_supported_bounded_with_other
end InitECandidate.Runtime
