import InitECandidate.Runtime.JournalDeleteBoundedOtherSupported
import InitECandidate.Runtime.JournalDeleteCallOtherSupported
import InitECandidate.Runtime.PanCallBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual jdel calls have a uniform bound across success and rejection. -/
theorem HashTableReady.jdel_call_supported_bounded_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 59 + keyLength.toNat + 9 ≤ state.clock)
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
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)]) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).2.clock + capacity.toNat * 59 + keyLength.toNat + 9 ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryReady := ready.after_read state entry keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have entryOther := otherReady.after_read state entry otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl
  have bounded := entryReady.jdel_body_supported_bounded_with_other entry keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity bits supported
    k sourceAligned (by change capacity.toNat * 59 + keyLength.toNat + 8 ≤ state.clock - 1; omega)
    wordDomain byteDomain sourceWordDomain sourceByteDomain t journalGlobal countGlobal capacityGlobal
    journalBound journalAligned journalOutside journalDomain
    otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits entryOther otherJournalOutside separated
  have installed : state.code.lookup (ofString "jdel") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_jdel,.one) := by
    rw [ready.live.arrays.code]; exact originalRuntimeCode_journalDelete_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "jdel") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_jdel) table key (by decide) installed
  have result := evaluate_call_body_bound state (ofString "jdel") [tableArgument,keyArgument]
    [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_jdel) callee .one
    (capacity.toNat * 59 + keyLength.toNat + 8) arguments lookup (by omega) (by change entry.clock ≤ (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).2.clock + (capacity.toNat * 59 + keyLength.toNat + 8); have cost := bounded.2.1; omega) bounded.2.2
  constructor
  · have cost := result.1
    omega
  · exact result.2

#print axioms HashTableReady.jdel_call_supported_bounded_with_other
end InitECandidate.Runtime
