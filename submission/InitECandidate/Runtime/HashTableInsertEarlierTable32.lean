import InitECandidate.Runtime.HashTableOutsideHeaderRegion32
import InitECandidate.Runtime.HashTableReadyIntervalFrame32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual insertion preserves an earlier allocated table even when it lies
between the target header and the target's relocated arrays. -/
theorem HashTableArraysInvariant32.insert_preserves_earlier_table {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock)
    (otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat)
    (separateHeader : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨
      table.toNat + 72 ≤ otherTable.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,cost,remaining,locals,globals,domain,endian,frame⟩ :=
    invariant.insert_preserves_outside_header state table keys stride capacity used values order orderPos count key value bits
      (otherOrderPos.toNat + otherCapacity.toNat * 8) beforeKeys beforeValues tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  have code : post.code = state.code := valid.code.trans invariant.code.symm
  have otherFrame : ∀ address : BitVec 64, otherTable.toNat ≤ address.toNat →
      address.toNat < otherOrderPos.toNat + otherCapacity.toNat * 8 → post.memory address = state.memory address := by
    intro address lower upper
    apply frame address ?_ upper
    rcases separateHeader with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  exact ⟨post,run,valid,otherReady.interval_frame state post otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
    otherFrame globals code domain endian,cost,remaining,locals,globals,domain,endian⟩

#print axioms HashTableArraysInvariant32.insert_preserves_earlier_table
end InitECandidate.Runtime
