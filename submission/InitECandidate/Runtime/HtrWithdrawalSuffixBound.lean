import InitECandidate.Runtime.HtrWithdrawalSource
import InitECandidate.Runtime.RunBoundedDiscardHeap
import InitECandidate.Runtime.HtrU64AtBound
import InitECandidate.Runtime.HtrBytesVectorReturnedHeap
import InitECandidate.Runtime.MerkleizeCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def WithdrawalLocals {F : Type} (state : PanSemStateFiniteExact 64 F) (w ch out : BitVec 64) : Prop :=
  state.locals.lookup (ofString "w") = some (.val (.word w)) ∧
  state.locals.lookup (ofString "ch") = some (.val (.word ch)) ∧
  state.locals.lookup (ofString "out") = some (.val (.word out))

def WithdrawalSuffixBound (index cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w ch out heap : BitVec 64), WithdrawalLocals state w ch out →
    state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) → heap.toNat ≤ 33806089496 →
    state.code = originalRuntimeCode → cost ≤ state.clock → RunBounded state (htrWithdrawalAt index) cost

theorem withdrawal_u64_step (index next cost : Nat) (arguments : List (ExpHOL 64))
    (source : htrWithdrawalAt index =
      .seq (.call (some (none,none)) (ofString "htr_u64_at") arguments) (htrWithdrawalAt next))
    (tail : WithdrawalSuffixBound next cost) : WithdrawalSuffixBound index (30 + cost) := by
  intro F state w ch out heap locals hh cap code budget
  rw [source]
  apply runBounded_discard_heap_seq state (ofString "htr_u64_at") arguments _ (ofString "heap_ptr") heap 30 cost
    (RunBounded.ofProg (ProgBounded.call htrU64At_funBounded _ _) code (by omega)) budget
  · intro post normal
    have globals := htrU64At_call_globals arguments state code
    rw [normal] at globals
    rw [globals]; exact hh
  · intro post keep heapKept postCode remaining
    exact tail post w ch out heap ⟨(keep _).trans locals.1,(keep _).trans locals.2.1,(keep _).trans locals.2.2⟩
      heapKept cap (postCode.trans code) remaining

def withdrawalMerkleCost : Nat := (merkleBodyCost + 1) + 1

theorem withdrawal_merkle_suffix : WithdrawalSuffixBound 6 withdrawalMerkleCost := by
  intro F state w ch out heap locals hh cap code budget
  rw [source_htrWithdrawal_merkle]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "ch"),.const 4,.const 4,.var .local (ofString "out")] =
      some [.val (.word ch),.val (.word (4#64)),.val (.word (4#64)),.val (.word out)] := by
    simp [evalListHOLExact,evalHOLExact,locals.2.1,locals.2.2]
  exact RunBounded.seq (runBounded_merkleize_call state none _ ch 4 4 out heap args (by decide) hh cap code
    (by unfold withdrawalMerkleCost at budget; omega)) budget (by
      intro post normal postCode remaining
      exact RunBounded.ofProg
        (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
        (postCode.trans code) remaining)

def withdrawalThirdCost : Nat := 30 + withdrawalMerkleCost

theorem withdrawal_third_suffix : WithdrawalSuffixBound 5 withdrawalThirdCost :=
  withdrawal_u64_step 5 6 withdrawalMerkleCost _ source_htrWithdrawal_u64_third withdrawal_merkle_suffix

def withdrawalVectorCost : Nat := (htrBytesVectorBodyCost + 1) + withdrawalThirdCost

theorem withdrawal_vector_suffix : WithdrawalSuffixBound 4 withdrawalVectorCost := by
  intro F state w ch out heap locals hh cap code budget
  rw [source_htrWithdrawal_vector]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.op .add [.var .local (ofString "w"),.const 16],.const 20,.op .add [.var .local (ofString "ch"),.const 64]] =
      some [.val (.word (w + (16#64))),.val (.word (20#64)),.val (.word (ch + (64#64)))] := by
    simp [evalListHOLExact,evalHOLExact,locals.1,locals.2.1,wordOpHOL,wordOp,valueIsWord,valueWord]
  apply runBounded_discard_heap_seq state (ofString "htr_bytes_vector") _ _ (ofString "heap_ptr") heap
    (htrBytesVectorBodyCost + 1) withdrawalThirdCost
    (runBounded_htrBytesVector_call state none _ (w + (16#64)) 20 (ch + (64#64)) heap args (by decide) hh cap code
      (by unfold withdrawalVectorCost at budget; omega)) budget
  · intro post normal
    exact htrBytesVector_call_normal_heap state post _ (w + (16#64)) 20 (ch + (64#64)) heap args code hh normal
  · intro post keep heapKept postCode remaining
    exact withdrawal_third_suffix post w ch out heap
      ⟨(keep _).trans locals.1,(keep _).trans locals.2.1,(keep _).trans locals.2.2⟩ heapKept cap (postCode.trans code) remaining

def withdrawalSecondCost : Nat := 30 + withdrawalVectorCost

theorem withdrawal_second_suffix : WithdrawalSuffixBound 3 withdrawalSecondCost :=
  withdrawal_u64_step 3 4 withdrawalVectorCost _ source_htrWithdrawal_u64_second withdrawal_vector_suffix

def withdrawalCallsCost : Nat := 30 + withdrawalSecondCost

theorem withdrawal_calls_suffix : WithdrawalSuffixBound 2 withdrawalCallsCost :=
  withdrawal_u64_step 2 3 withdrawalSecondCost _ source_htrWithdrawal_u64_first withdrawal_second_suffix

#print axioms withdrawal_u64_step
#print axioms withdrawal_merkle_suffix
#print axioms withdrawal_third_suffix
#print axioms withdrawal_vector_suffix
#print axioms withdrawal_second_suffix
#print axioms withdrawal_calls_suffix
end InitECandidate.Runtime
