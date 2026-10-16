import InitECandidate.Runtime.HashTableSetNoGrowthOrder32
import InitECandidate.Runtime.OriginalHashSetCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original set call below the growth threshold, including argument
binding, call entry and restoration of caller locals. -/
theorem HashTableArraysInvariant32.set_call_no_growth_order {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + 38 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos nextCount bits post ∧
      HashOrderEntriesBound order capacity nextCount post ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + 38 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
  have entryValid : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits entry :=
    invariant.after_read state entry table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  obtain ⟨nextCount,post,counts,body,valid,postEntries,cost,remaining,globals,code,addresses,endian⟩ :=
    entryValid.set_no_growth_order entry table keys stride capacity used values order orderPos count key value bits t k v keyAligned sourceWordDomain sourceByteDomain loadFactor
      (by change 3 * capacity.toNat + 37 ≤ state.clock - 1; omega)
      (entries.after_memory state entry order capacity count rfl)
  have installed : state.code.lookup (ofString "htab_set") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_set,.one) := by
    rw [invariant.code]; exact originalRuntimeCode_hashSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") (sourceFunctionBody Guest.guestFn_htab_set)
    table key value (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_htab_set) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨nextCount,{post with locals := state.locals},counts,call,
    valid.after_read post _ table keys stride capacity used values order orderPos nextCount bits rfl rfl rfl rfl,postEntries.after_memory post _ order capacity nextCount rfl,?_,?_,rfl,globals,code,addresses,endian⟩
  · change state.clock ≤ post.clock + 3 * capacity.toNat + 38
    change state.clock - 1 ≤ post.clock + 3 * capacity.toNat + 37 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms HashTableArraysInvariant32.set_call_no_growth_order
end InitECandidate.Runtime
