import InitECandidate.Runtime.JournalDeleteBodyOtherSupported
import InitECandidate.Runtime.OriginalJournalDeleteCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original journal deletion call with caller-local restoration and both outcomes. -/
theorem HashTableReady.jdel_call_supported_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (request : keyLength ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 59 + keyLength.toNat + 9 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (inside : count.toNat < journalCapacity.toNat)
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument]) = (none,post) ∧
      ((HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨
       (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer keyLength) post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) post)) ∧
      state.clock ≤ post.clock + capacity.toNat * 59 + keyLength.toNat + 9 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
  obtain ⟨post,body,cases,cost,remaining,code,domain,endian⟩ :=
    entryReady.jdel_body_supported_with_other entry keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity bits supported
      k request sourceAligned (by change capacity.toNat * 59 + keyLength.toNat + 8 ≤ state.clock - 1; omega)
      wordDomain byteDomain sourceWordDomain sourceByteDomain t journalGlobal countGlobal capacityGlobal
      inside journalBound journalAligned journalOutside journalDomain
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits entryOther otherJournalOutside separated
  have installed : state.code.lookup (ofString "jdel") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_jdel,.one) := by
    rw [ready.live.arrays.code]; exact originalRuntimeCode_journalDelete_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "jdel") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_jdel) table key (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "jdel")
    [tableArgument,keyArgument] [.val (.word table),.val (.word key)]
    (sourceFunctionBody Guest.guestFn_jdel) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  let restored := {post with locals := state.locals}
  refine ⟨restored,call,?_,?_,?_,rfl,code,domain,endian⟩
  · rcases cases with ⟨unchanged,otherUnchanged⟩ | deleted
    · exact Or.inl ⟨unchanged.after_read post restored keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl,
        otherUnchanged.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl⟩
    · obtain ⟨remaining,counts,valid,otherValid⟩ := deleted
      exact Or.inr ⟨remaining,counts,valid.after_read post restored keyLength table keys stride capacity used values order orderPos remaining bits
        (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl,
        otherValid.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl⟩
  · dsimp only [restored]
    change state.clock - 1 ≤ post.clock + capacity.toNat * 59 + keyLength.toNat + 8 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms HashTableReady.jdel_call_supported_with_other
end InitECandidate.Runtime
