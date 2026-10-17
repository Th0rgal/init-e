import InitECandidate.Runtime.HashDeleteBodyValuesIn
import InitECandidate.Runtime.OriginalHashDeleteCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion call with caller-local restoration and call-entry cost. -/
theorem evaluate_hashDelete_call_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (keyValueOrder : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (budget : capacity.toNat * 57 + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      HashTableValuesIn table targets post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + 3 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.locals = state.locals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,body,postRegistered,cost,remaining,globals,code,domain,endian⟩ := evaluate_source_hashDelete_values_in entry
    keyLength table keys stride capacity used values order orderPos items key bits supported
    (invariant.after_read state entry keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl)
    (entries.after_read state entry used values capacity rfl rfl rfl)
    (reverse.after_read state entry used orderPos capacity items rfl rfl rfl)
    (ordered.after_memory state entry order capacity items rfl)
    (linked.after_read state entry used order orderPos capacity items rfl rfl rfl)
    keyValueOrder t k keyAligned keyWords keyBytes targets (registered.after_read rfl rfl rfl) (by change capacity.toNat * 57 + 2 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "htab_del") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_del,.one) := by
    rw [invariant.code]; exact originalRuntimeCode_hashDelete_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_del") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_del) table key (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_del")
    [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_del)
    callee .one (.val (.word result)) post arguments lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals},call,postRegistered.after_read rfl rfl rfl,?_,?_,globals,code,domain,endian,rfl⟩
  · change state.clock ≤ post.clock + capacity.toNat * 57 + 3
    change state.clock - 1 ≤ post.clock + capacity.toNat * 57 + 2 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms evaluate_hashDelete_call_values_in
end InitECandidate.Runtime
