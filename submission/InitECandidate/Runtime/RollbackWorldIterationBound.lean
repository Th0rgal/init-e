import InitECandidate.Runtime.RollbackWorld
import InitECandidate.Runtime.StateRestoreIterationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The concrete world supplies all table/key/record premises of the actual
iteration bound. No safe-allocation-plan assumption is needed for this cost bound. -/
theorem RollbackWorld.iteration_bounded {F : Type} {widths : BitVec 64 → BitVec 64}
    {tables : Set (BitVec 64)} {journal snapshot count : BitVec 64}
    {state : PanSemStateFiniteExact 64 F} (valid : RollbackWorld widths tables journal snapshot count state)
    (active : 0 < stateRestoreRank state) (ticks : 2 ^ 72 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    state.clock ≤ (evaluateHOLFiniteState state stateRestoreLoopBody).2.clock + 2 ^ 72 ∧
      (evaluateHOLFiniteState state stateRestoreLoopBody).2.clock ≤ state.clock := by
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
  apply ready.restore_iteration_bounded state (widths table) table pointer keys stride capacity used values order orderPos items key journal count present value bits
    supported strideBound large ticks (fun address _ upper => heapDomain address upper) valid.journalGlobal valid.counter
    (by simpa using domains 0 (by simp)) t
    (domains 8 (by simp)) k (domains 16 (by simp)) p (domains 24 (by simp)) v aligned words bytes

#print axioms RollbackWorld.iteration_bounded
end InitECandidate.Runtime
