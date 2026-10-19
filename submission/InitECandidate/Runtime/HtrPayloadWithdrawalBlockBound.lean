import InitECandidate.Runtime.HtrPayloadWithdrawalHashBound
import InitECandidate.Runtime.VmFn_heap_release
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrPayloadWithdrawalRelease : ProgHOL 64 :=
  .call (some (none,none)) (ofString "heap_release") [.var .local (ofString "m2")]

def htrPayloadWithdrawalBlock : ProgHOL 64 :=
  .seq (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) (.seq htrPayloadWithdrawalHashCall htrPayloadWithdrawalRelease)

theorem source_htrPayload_withdrawal_release : htrPayloadAt 30 =
    .seq htrPayloadWithdrawalRelease (htrPayloadAt 31) := by rfl

theorem evaluate_htrPayload_withdrawal_block_source {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (htrPayloadAt 28) =
      evaluateHOLFiniteState state (.seq htrPayloadWithdrawalBlock (htrPayloadAt 31)) := by
  rw [source_htrPayload_withdrawals,source_htrPayload_withdrawal_hash,source_htrPayload_withdrawal_release]
  unfold htrPayloadWithdrawalBlock
  rw [evaluate_seq_assoc]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_seq_line780]
  cases loop : evaluateHOLFiniteState state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) with
  | mk result post =>
    cases result with
    | none => exact (evaluate_seq_assoc post htrPayloadWithdrawalHashCall htrPayloadWithdrawalRelease (htrPayloadAt 31)).symm
    | some result => rfl

theorem runBounded_htrPayload_withdrawal_block (array roots heap count : BitVec 64)
    (countBound : count.toNat ≤ 134217712) (heapFits : heap.toNat ≤ 33806089496)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) (chunks : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (valid : HtrPayloadWithdrawalState array roots heap count state rank)
    (chunksLocal : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (budget : rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2) ≤ state.clock) :
    RunBounded state htrPayloadWithdrawalBlock (rank * (htrWithdrawalBodyCost + 2) + (htrPlistChunksCost + 2)) := by
  have loop := htrPayload_withdrawal_loop_ranked array roots heap count countBound heapFits rank state code valid (by omega)
  have loopBound : RunBounded state (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep)
      (rank * (htrWithdrawalBodyCost + 2)) := ⟨loop.1,loop.2.1,loop.2.2.1⟩
  exact RunBounded.seq loopBound budget (by
    intro next normal nextCode remaining
    have nextLoop := loop
    rw [normal] at nextLoop
    obtain ⟨nextRank,nextValid,_,_⟩ := nextLoop.2.2.2 rfl
    have atChunks := (htrPayload_withdrawal_loop_local_frame state next (ofString "ch") (by decide) normal).trans chunksLocal
    have hashed := runBounded_htrPayload_withdrawal_hash next roots count chunks heap nextValid.rootsLocal
      nextValid.countLocal atChunks nextValid.heapGlobal countBound heapFits (nextCode.trans code) (by omega)
    have combined := RunBounded.seq (tail := htrPayloadWithdrawalRelease) (b := 1) hashed (by omega) (by
      intro released releaseNormal releaseCode releaseBudget
      apply RunBounded.ofProg _ (releaseCode.trans (nextCode.trans code)) releaseBudget
      exact ProgBounded.call vmBound_heap_release _ _)
    simpa only [Nat.add_assoc] using combined)

#print axioms evaluate_htrPayload_withdrawal_block_source
#print axioms source_htrPayload_withdrawal_release
#print axioms runBounded_htrPayload_withdrawal_block
end InitECandidate.Runtime
