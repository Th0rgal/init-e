import InitECandidate.Runtime.HashTableReadyInsertPhysicalFrameSupported
import InitECandidate.Runtime.HashTableValuesInPhysicalFrame
import InitECandidate.Runtime.HashTableReadyInsertSupported
import InitECandidate.Runtime.HashTablePhysicalInsertionSeparation
import InitECandidate.Runtime.HashTableReadyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual insertion preserves an earlier allocated table even when it lies
between the target header and the target's relocated arrays. -/
theorem HashTableReady.insert_other_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (otherKeyLength otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn otherTable targets state)
    (separated : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos (count + 1) bits pointer post ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherPointer post ∧
      HashTableValuesIn otherTable targets post ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,frame,cost,remaining,locals,globals,domain,endian⟩ :=
    ready.insert_supported_with_physical_frame state keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  have code : post.code = state.code := valid.live.arrays.code.trans ready.live.arrays.code.symm
  have otherFrame : ∀ address : BitVec 64, tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address →
      post.memory address = state.memory address := by
    intro address belongs
    exact frame address (fun target => separated address target belongs)
  exact ⟨post,run,valid,
    otherReady.physical_frame state post otherKeyLength otherTable otherPointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherFrame globals code domain endian,
    registered.physical_frame state post otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady.live.arrays targets otherFrame domain endian,
    cost,remaining,locals,globals,domain,endian⟩

#print axioms HashTableReady.insert_other_values_in
end InitECandidate.Runtime
