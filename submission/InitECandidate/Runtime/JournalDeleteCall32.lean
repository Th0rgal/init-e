import InitECandidate.Runtime.JournalDeleteBody32
import InitECandidate.Runtime.OriginalJournalDeleteCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original journal deletion call with caller-local restoration and both outcomes. -/
theorem HashTableReady32.jdel_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 39 + 41 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument]) = (none,post) ∧
      ((HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post) ∨
       (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer 32) post)) ∧
      state.clock ≤ post.clock + capacity.toNat * 39 + 41 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryReady := ready.after_read state entry table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  obtain ⟨post,body,cases,cost,remaining,code,domain,endian⟩ :=
    entryReady.jdel_body entry table pointer keys stride capacity used values order orderPos items key journal count journalCapacity bits
      k request sourceAligned (by change capacity.toNat * 39 + 40 ≤ state.clock - 1; omega)
      wordDomain byteDomain sourceWordDomain sourceByteDomain t journalGlobal countGlobal capacityGlobal
      inside journalBound journalAligned journalOutside journalDomain
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
  · rcases cases with unchanged | deleted
    · exact Or.inl (unchanged.after_read post restored table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl)
    · obtain ⟨remaining,counts,valid⟩ := deleted
      exact Or.inr ⟨remaining,counts,valid.after_read post restored table keys stride capacity used values order orderPos remaining bits
        (allocationEnd pointer 32) rfl rfl rfl rfl rfl⟩
  · dsimp only [restored]
    change state.clock - 1 ≤ post.clock + capacity.toNat * 39 + 40 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms HashTableReady32.jdel_call
end InitECandidate.Runtime
