import InitECandidate.Runtime.RollbackWorldIterationFields
import InitECandidate.Runtime.RollbackWorldIterationBound
import InitECandidate.Runtime.HashSetRegistryCostCeiling
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A live separated world executes the actual rollback body within the uniform
clock budget, preserving the smaller world and separation. Allocation success
is explicit and will be discharged or replaced by a terminal failure branch. -/
theorem RollbackWorld.iteration_bounded_fields {F : Type} {widths : BitVec 64 → BitVec 64}
    {tables : Set (BitVec 64)} {journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F} (valid : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (active : 0 < stateRestoreRank state) (ticks : 2 ^ 72 + 1 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (ts fieldPointer : BitVec 64)
    (tsFields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (headers : ∀ table ∈ tables, ts.toNat + 72 ≤ table.toNat) :
    ∃ result post, evaluateHOLFiniteState state stateRestoreLoopBody = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 72 + 1) ∧ post.clock ≤ state.clock ∧
      ((result = none ∧ RollbackWorld widths tables journal snapshot (count - 1) post ∧ RollbackPhysicalSeparated widths tables post ∧
        stateRestoreRank post < stateRestoreRank state ∧ StateFreshTxFields ts fieldPointer stateFreshTxAllTables post ∧
        (∀ name, name ≠ Flapjack.Basis.Pure.MlString.ofString "heap_ptr" → name ≠ Flapjack.Basis.Pure.MlString.ofString "journal_n" → post.globals.lookup name = state.globals.lookup name)) ∨
       (result ≠ none ∧ result ≠ some .timeOut ∧ result ≠ some .continue ∧ result ≠ some .break ∧ (∀ output : ValueHOL 64, result ≠ some (.returned output)))) := by
  obtain ⟨table,key,present,value,tableReady,supported,t,k,p,v,aligned,words,bytes⟩ := valid.select_last active
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,strideBound,large⟩ := tableReady
  have rank := stateRestoreRank_of_bindings state count snapshot valid.counter valid.snapshotLocal
  have numeric := (stateRestore_rank_decreases count snapshot (by omega)).1
  have inside : (count - 1).toNat < count.toNat := by omega
  obtain ⟨_,_,_,_,_,_,_,_,_,_,fields,_⟩ := valid.records.1 (count - 1).toNat inside
  have indexWord : BitVec.ofNat 64 (count - 1).toNat = count - 1 := by
    apply BitVec.eq_of_toNat_eq
    change (count - 1).toNat % 2 ^ 64 = (count - 1).toNat
    exact Nat.mod_eq_of_lt (count - 1).isLt
  have domains : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (journal + (count - 1) * 32 + BitVec.ofNat 64 offset) := by
    simpa only [indexWord] using fields
  have registered : table ∈ tables := by
    apply valid.references (count - 1).toNat inside table
    simpa only [indexWord] using t
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have setCeiling := hashSetRegistryCost_le_ceiling capacity (widths table) items capacityBound supported (Nat.le_of_lt ready.live.arrays.room)
  have outcome := RollbackWorld.iteration_all_plans_fields state widths tables
    table pointer keys stride capacity used values order orderPos items key journal count present value bits supported ready strideBound large
    (by change hashSetRegistryCost capacity (widths table) items ≤ state.clock; omega) (by omega)
    (fun address _ upper => heapDomain address upper)
    (by simpa using domains 0 (by simp)) t
    (domains 8 (by simp)) k (domains 16 (by simp)) p (domains 24 (by simp)) v aligned words bytes
    snapshot valid registered separated (by omega) ts fieldPointer tsFields (headers table registered) ticks heapDomain
  have cost := valid.iteration_bounded active (by omega) heapDomain
  rcases outcome with success | failure
  · obtain ⟨post,run,worldPost,separatedPost,rankPost,postFields,globals⟩ := success
    rw [run] at cost
    exact ⟨none,post,run,by exact cost.1.trans (Nat.add_le_add_left (Nat.le_succ _) _),cost.2,Or.inl ⟨rfl,worldPost,separatedPost,rankPost,postFields,globals⟩⟩
  · exact ⟨_,_,rfl,by exact cost.1.trans (Nat.add_le_add_left (Nat.le_succ _) _),cost.2,Or.inr ⟨failure.1,failure.2.1,failure.2.2.2.1,failure.2.2.2.2,failure.2.2.1⟩⟩

#print axioms RollbackWorld.iteration_bounded_fields
end InitECandidate.Runtime
