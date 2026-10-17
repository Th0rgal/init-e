import InitECandidate.Runtime.HashTableSetCallNoGrowthPhysicalFrameSupported
import InitECandidate.Runtime.HashTableValuesInSetNoGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual no-growth htab_set calls retain registered values and the full table
invariant, including their call entry and caller-local restoration. -/
theorem HashTableReady.set_call_no_growth_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + keyLength.toNat + 6 ≤ state.clock)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      HashTableValuesIn table targets post ∧
      (∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address → post.memory address = state.memory address) ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 6 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
  have entryReady := ready.after_read state entry keyLength table keys stride capacity used values order orderPos count bits pointer rfl rfl rfl rfl rfl
  obtain ⟨nextCount,post,counts,body,postReady,postRegistered,frame,cost,remaining,globals,code,domain,endian⟩ :=
    entryReady.set_no_growth_values_in entry keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
      t k v keyAligned sourceWordDomain sourceByteDomain loadFactor (by change 3 * capacity.toNat + keyLength.toNat + 5 ≤ state.clock - 1; omega) targets (entries.after_read rfl rfl rfl) member
  have installed : state.code.lookup (ofString "htab_set") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_set,.one) := by
    rw [ready.live.arrays.code]; exact originalRuntimeCode_hashSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_htab_set) table key value (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_htab_set) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  let restored := {post with locals := state.locals}
  refine ⟨nextCount,restored,counts,call,
    postReady.after_read post restored keyLength table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl,
    postRegistered.after_read rfl rfl rfl,frame,
    ?_,?_,rfl,globals,code,domain,endian⟩
  · change state.clock ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 6
    change state.clock - 1 ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 5 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms HashTableReady.set_call_no_growth_values_in
end InitECandidate.Runtime
