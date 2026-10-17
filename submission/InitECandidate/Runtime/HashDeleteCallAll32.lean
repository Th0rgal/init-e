import InitECandidate.Runtime.HashDeleteBodyAll32
import InitECandidate.Runtime.OriginalHashDeleteCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion call with caller-local restoration and call-entry cost. -/
theorem evaluate_hashDelete32_call_all {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument : ExpHOL 64)
    (table keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (budget : capacity.toNat * 37 + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 3 ∧ post.clock ≤ state.clock ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableArraysInvariant32 table keys stride capacity used values order orderPos remaining bits post ∧
        HashValueEntriesWord used values capacity post ∧ HashOrderEntriesBound order capacity remaining post ∧
        HashReverseEntriesBound used orderPos capacity remaining post ∧ HashOrderLinked used order orderPos capacity remaining post) ∧
      post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,body,cost,remaining,outcome⟩ := evaluate_source_hashDelete32_all entry
    table keys stride capacity used values order orderPos items key bits
    (invariant.after_read state entry table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl)
    (entries.after_read state entry used values capacity rfl rfl rfl)
    (reverse.after_read state entry used orderPos capacity items rfl rfl rfl)
    (ordered.after_memory state entry order capacity items rfl)
    (linked.after_read state entry used order orderPos capacity items rfl rfl rfl)
    keyValueOrder t k keyAligned keyDomain (by change capacity.toNat * 37 + 2 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "htab_del") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_del,.one) := by
    rw [invariant.code]; exact originalRuntimeCode_hashDelete_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_del") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_del) table key (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_del")
    [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_del)
    callee .one (.val (.word result)) post arguments lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals},call,?_,?_,?_,rfl⟩
  · change state.clock ≤ post.clock + capacity.toNat * 37 + 3
    change state.clock - 1 ≤ post.clock + capacity.toNat * 37 + 2 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · rcases outcome with ⟨_,arrays,words,orderEntries,reverseEntries,postLinked⟩ | ⟨_,arrays,words,orderEntries,reverseEntries,postLinked⟩
    · exact ⟨items,Or.inl rfl,
        arrays.after_read post _ table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
        words.after_read post _ used values capacity rfl rfl rfl,
        orderEntries.after_memory post _ order capacity items rfl,
        reverseEntries.after_read post _ used orderPos capacity items rfl rfl rfl,
        postLinked.after_read post _ used order orderPos capacity items rfl rfl rfl⟩
    · exact ⟨items - 1,Or.inr rfl,
        arrays.after_read post _ table keys stride capacity used values order orderPos (items - 1) bits rfl rfl rfl rfl,
        words.after_read post _ used values capacity rfl rfl rfl,
        orderEntries.after_memory post _ order capacity (items - 1) rfl,
        reverseEntries.after_read post _ used orderPos capacity (items - 1) rfl rfl rfl,
        postLinked.after_read post _ used order orderPos capacity (items - 1) rfl rfl rfl⟩

#print axioms evaluate_hashDelete32_call_all
end InitECandidate.Runtime
