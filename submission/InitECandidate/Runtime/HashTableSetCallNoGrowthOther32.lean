import InitECandidate.Runtime.HashTableSetNoGrowthOther32
import InitECandidate.Runtime.OriginalHashSetCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual no-growth set call preserves both live tables and caller locals. -/
theorem HashTableReady32.set_call_no_growth_with_earlier_table {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos count bits pointer state)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + 38 ≤ state.clock)
    (otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat)
    (separateHeader : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)]) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableReady32 table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer post ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + 38 ∧ post.clock ≤ state.clock ∧
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
  have entryReady := ready.after_read state entry table keys stride capacity used values order orderPos count bits pointer rfl rfl rfl rfl rfl
  have otherEntry := otherReady.after_read state entry otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer rfl rfl rfl rfl rfl
  obtain ⟨nextCount,post,counts,body,postReady,postOther,cost,remaining,globals,code,domain,endian⟩ :=
    entryReady.set_no_growth_with_earlier_table entry table pointer keys stride capacity used values order orderPos count key value bits
      t k v keyAligned sourceWordDomain sourceByteDomain loadFactor (by change 3 * capacity.toNat + 37 ≤ state.clock - 1; omega)
      otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
      otherEntry beforeKeys beforeValues separateHeader
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
    postReady.after_read post restored table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl,
    postOther.after_read post restored otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer rfl rfl rfl rfl rfl,
    ?_,?_,rfl,globals,code,domain,endian⟩
  · change state.clock ≤ post.clock + 3 * capacity.toNat + 38
    change state.clock - 1 ≤ post.clock + 3 * capacity.toNat + 37 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms HashTableReady32.set_call_no_growth_with_earlier_table
end InitECandidate.Runtime
