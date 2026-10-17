import InitECandidate.Runtime.StateRestoreRank
import InitECandidate.Runtime.HashTableReadySetCallHeapFrameSupported
import InitECandidate.Runtime.HashSetSupportedCostCeiling
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Restoring a value, including table growth, preserves the journal rank and full table invariant. -/
theorem HashTableReady.restore_record_set_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key record present value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16))
    (presentCell : state.memory (record + 16) = .word present)
    (notZero : present ≠ (0#64))
    (valueDomain : state.memaddrs (record + 24)) (valueCell : state.memory (record + 24) = .word value)
    (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state stateRestoreRecordDecision = (none,post) ∧
      ((∃ remaining : BitVec 64, (remaining = items ∨ remaining = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits pointer post) ∨
       HashTableReady keyLength table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post) ∧
      stateRestoreRank post = stateRestoreRank state ∧
      state.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ state.clock := by
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have u := ready.live.arrays.usedBefore
    have o := ready.live.arrays.orderBefore
    have e := ready.live.arrays.endBound
    omega
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word present)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 16 r]
    simp [memLoadHOLExact]
    exact ⟨presentDomain,presentCell⟩
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
    rw [evalHOLExact,loaded]
    simp [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL,notZero]
  have loadedValue : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 24)) = some (.val (.word value)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 24 r]
    simp [memLoadHOLExact]
    exact ⟨valueDomain,valueCell⟩
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)] = some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp only [evalListHOLFinite,evalListHOLExact]
    rw [loadedValue]
    simp [evalHOLExact,t,k]
  have ceiling := hashSetSupportedCost_le_ceiling capacity keyLength items capacityBound supported (Nat.le_of_lt ready.live.arrays.room)
  obtain ⟨post,run,postReady,cost,remaining,_,_,_,_,_,rank⟩ := ready.set_call_supported_heap_frame state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
    strideBound ready.live.frontier.aligned ready.live.frontier.bounded capacityBound safePlan
    (by change hashSetSupportedCost capacity keyLength items ≤ state.clock; omega)
    ready.live.frontier.heap domain _ _ _ args capacityLarge keyAligned keyWords keyBytes
  unfold hashSetSupportedCost at ceiling
  refine ⟨post,?_,postReady,rank,by omega,remaining⟩
  · unfold stateRestoreRecordDecision
    rw [evaluateHOLFiniteState_ite,condition]
    simpa using run

#print axioms HashTableReady.restore_record_set_preserves
end InitECandidate.Runtime
