import InitECandidate.Runtime.StateInitHeapBoundCombinators
import InitECandidate.Runtime.HtabBlockInit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual constructor-list cost, including each real function-call tick. -/
def stateInitTableListCost : List (Nat×Nat×Nat)→Nat
 | []=>0
 | (_,capacity,_)::rest=>htabNewCost (BitVec.ofNat 64 capacity)+1+stateInitTableListCost rest

/-- Exact original fixed table constructor lists, with failure paths included. -/
theorem state_init_table_list_bounded (tables : List (Nat×Nat×Nat)) (tail : ProgHOL 64) (cost : Nat)
 (bounded : StateInitHeapBounded tail cost) :
 StateInitHeapBounded (blockCtorSeq tables tail) (stateInitTableListCost tables+cost) := by
 induction tables with
 | nil =>
  intro F s code heap budget
  simpa only [blockCtorSeq,stateInitTableListCost,Nat.zero_add] using bounded s code heap (by simpa only [stateInitTableListCost,Nat.zero_add] using budget)
 | cons item rest ih =>
  obtain ⟨width,capacity,offset⟩ := item
  unfold blockCtorSeq stateInitTableListCost
  have stored : StateInitHeapBounded (.seq (blockPointerStore offset) (blockCtorSeq rest tail)) (stateInitTableListCost rest+cost) := by
   intro F s code heap budget
   exact state_init_store_seq_bounded _ _ ih s code heap budget
  intro F s code heap budget
  have ticks : htabNewCost (BitVec.ofNat 64 capacity)+1+(stateInitTableListCost rest+cost)≤s.clock := by
   simpa only [Nat.add_assoc] using budget
  have step := state_init_table_seq_bounded (ofString "t") (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) stored s code heap ticks
  simpa only [Nat.add_assoc] using step

/-- Actual block record, all seven fixed-capacity tables, and final scratch/journal
allocations: finite bound with a typed capped heap, with no allocation room premise. -/
theorem state_init_block_tail_bounded : StateInitHeapBounded
 (stateInitSpineDrop 8 (sourceFunctionBody Guest.guestFn_state_init)) 364 := by
 rw [source_stateInit_block]
 have final : StateInitHeapBounded (stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init)) 4 := by
  intro F s code _ budget
  exact state_init_final_tail_bounded s code budget
 let tail := stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init)
 have last : StateInitHeapBounded (blockCtorSeq blockTablesLast tail) (stateInitTableListCost blockTablesLast+4) := by
  intro F s code heap budget
  exact state_init_table_list_bounded blockTablesLast tail 4 final s code heap budget
 let zeroTail : ProgHOL 64 := .seq (.store (.op .add [.var .global (ofString "bs"),.const 56]) (.const 0))
  (.seq (.store (.op .add [.var .global (ofString "bs"),.const 64]) (.const 0)) (blockCtorSeq blockTablesLast tail))
 have zeros : StateInitHeapBounded zeroTail (stateInitTableListCost blockTablesLast+4) := by
  intro F s code heap budget
  exact state_init_store_seq_bounded _ _ (state_init_store_seq_bounded _ _ last) s code heap budget
 have first : StateInitHeapBounded (blockCtorSeq blockTablesFirst zeroTail)
  (stateInitTableListCost blockTablesFirst+(stateInitTableListCost blockTablesLast+4)) := by
  intro F s code heap budget
  exact state_init_table_list_bounded blockTablesFirst zeroTail _ zeros s code heap budget
 have base : StateInitHeapBounded (.seq (.store (.op .add [.var .global (ofString "bs"),.const 0])
  (.var .global (ofString "ws"))) (blockCtorSeq blockTablesFirst zeroTail))
  (stateInitTableListCost blockTablesFirst+(stateInitTableListCost blockTablesLast+4)) := by
  intro F s code heap budget
  exact state_init_store_seq_bounded _ _ first s code heap budget
 intro F s code heap budget
 have cost : 2+(stateInitTableListCost blockTablesFirst+(stateInitTableListCost blockTablesLast+4))=364 := by decide
 have allocated := state_init_alloc_seq_bounded .global (ofString "bs") [.const 80] (Or.inr (by decide)) base
  s code heap (by rw [cost];exact budget)
 exact allocated

#print axioms state_init_table_list_bounded
#print axioms state_init_block_tail_bounded
end InitECandidate.Runtime
