import InitECandidate.Runtime.StateInitStorageTableTailBound
import InitECandidate.Runtime.StateFreshTxSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Every actual fixed transaction-state constructor and pointer store,
including allocation failures, keeps the real heap frontier for its suffix. -/
theorem state_fresh_tx_table_sequence_bounded (tables : List (Nat×Nat×Nat)) (tail : ProgHOL 64) (cost : Nat)
 (bounded : StateInitHeapBounded tail cost) :
 StateInitHeapBounded (stateFreshTxConstructorSequence tables tail) (stateInitTableListCost tables+cost) := by
 induction tables with
 | nil =>
  intro F s code heap budget
  simpa only [stateFreshTxConstructorSequence,stateInitTableListCost,Nat.zero_add] using
   bounded s code heap (by simpa only [stateInitTableListCost,Nat.zero_add] using budget)
 | cons item rest ih =>
  obtain ⟨width,capacity,offset⟩ := item
  unfold stateFreshTxConstructorSequence stateInitTableListCost
  have stored : StateInitHeapBounded (.seq (stateFreshTxPointerStore offset)
   (stateFreshTxConstructorSequence rest tail)) (stateInitTableListCost rest+cost) := by
   intro F s code heap budget
   exact state_init_store_seq_bounded _ _ ih s code heap budget
  intro F s code heap budget
  have ticks : htabNewCost (BitVec.ofNat 64 capacity)+1+(stateInitTableListCost rest+cost)≤s.clock := by
   simpa only [Nat.add_assoc] using budget
  have step:=state_init_table_seq_bounded (ofString "t") (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity)
   stored s code heap ticks
  simpa only [Nat.add_assoc] using step

/-- Complete original state_fresh_tx body: a concrete aligned/capped heap
suffices for a finite all-outcomes bound. No arena room, table-validity or
successful-callee/runtime premise is assumed. -/
theorem state_fresh_tx_body_bounded : StateInitHeapBounded
 (sourceFunctionBody Guest.guestFn_state_fresh_tx) 1000 := by
 rw [source_stateFreshTx_body]
 let tail : ProgHOL 64 := .seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0))
 have final : StateInitHeapBounded tail 0 := by
  intro F s code _ budget
  exact RunBounded.ofProg (ProgBounded.straight tail rfl) code budget
 have tables : StateInitHeapBounded (stateFreshTxConstructorSequence stateFreshTxRemainingTables tail)
  (stateInitTableListCost stateFreshTxRemainingTables+0) := by
  intro F s code heap budget
  exact state_fresh_tx_table_sequence_bounded stateFreshTxRemainingTables tail 0 final s code heap budget
 have stored : StateInitHeapBounded (.seq (stateFreshTxPointerStore 8)
  (stateFreshTxConstructorSequence stateFreshTxRemainingTables tail))
  (stateInitTableListCost stateFreshTxRemainingTables+0) := by
  intro F s code heap budget
  exact state_init_store_seq_bounded _ _ tables s code heap budget
 have declared : StateInitHeapBounded (.decCall (ofString "t") .one (ofString "htab_new") [.const 20,.const 64]
  (.seq (stateFreshTxPointerStore 8) (stateFreshTxConstructorSequence stateFreshTxRemainingTables tail)))
  (htabNewCost 64+1+(stateInitTableListCost stateFreshTxRemainingTables+0)) := by
  intro F s code heap budget
  exact state_init_table_declaration_bounded (ofString "t") 20 64 stored s code heap budget
 have base : StateInitHeapBounded (.seq
  (.store (.op .add [.var .global (ofString "ts"),.const 0]) (.var .global (ofString "bs")))
  (.decCall (ofString "t") .one (ofString "htab_new") [.const 20,.const 64]
   (.seq (stateFreshTxPointerStore 8) (stateFreshTxConstructorSequence stateFreshTxRemainingTables tail))))
  (htabNewCost 64+1+(stateInitTableListCost stateFreshTxRemainingTables+0)) := by
  intro F s code heap budget
  exact state_init_store_seq_bounded _ _ declared s code heap budget
 have costLe : 2+(htabNewCost 64+1+(stateInitTableListCost stateFreshTxRemainingTables+0))≤1000 := by decide
 intro F s code heap budget
 exact (state_init_alloc_seq_bounded .global (ofString "ts") [.const 72] (Or.inr (by decide)) base
  s code heap (by omega)).weaken costLe
#print axioms state_fresh_tx_table_sequence_bounded
#print axioms state_fresh_tx_body_bounded
end InitECandidate.Runtime
