import InitECandidate.Runtime.HtrPayloadRequestsSuffixMemory
import InitECandidate.Runtime.HtrPayloadPostWithdrawalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def PayloadPostWithdrawalMemory (index cost : Nat) : Prop :=
  ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk heap payload raw chunks out mark pointer length watched : BitVec 64) (value : ValueHOL 64),
    ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched →
    PayloadFinalLocals state payload raw chunks out →
    state.locals.lookup (ofString "mark") = some (.val (.word mark)) →
    RlpSliceEntry state payload (4#64) pointer length → length.toNat ≤ 134217712 →
    chunks.toNat % 8 = 0 → chunks.toNat + 608 ≤ 33806089496 → payload.toNat + 72 < chunks.toNat →
    watched.toNat < chunks.toNat → cost ≤ state.clock →
    evaluateHOLFiniteState state (htrPayloadAt index) = (some (.returned value),post) →
    post.memory watched = state.memory watched

/-- A scalar hash step retains both the watched word and the request metadata
needed by the actual remaining payload suffix. -/
theorem payload_final_u64_memory_step (index next cost : Nat) (inputOffset outputOffset : BitVec 64)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.op .add [.var .local (ofString "raw"),.const inputOffset],
       .op .add [.var .local (ofString "ch"),.const outputOffset]]) (htrPayloadAt next))
    (tail : PayloadPostWithdrawalMemory next cost) : PayloadPostWithdrawalMemory index (30 + cost) := by
  intro F state post sha accelerator zeroHashes chunk heap payload raw chunks out mark pointer length watched value
    layout locals atMark entry small aligned fits before watchedBefore budget run
  rw [source] at run
  obtain ⟨middle,normal,rest⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ rfl state v) run
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "raw"),.const inputOffset],
     .op .add [.var .local (ofString "ch"),.const outputOffset]]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word (raw + inputOffset)),.val (.word (chunks + outputOffset))] := by
    simp [arguments,evalListHOLExact,evalHOLExact,locals.2.1,locals.2.2.1,wordOpHOL,wordOp,valueIsWord,valueWord]
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have outputMod : (chunks + outputOffset).toNat % 8 = 0 := by rw [natural,Nat.add_mod,aligned,outputAligned]
  have frame := htrU64At_call_normal_memory state middle arguments (raw + inputOffset) (chunks + outputOffset) watched
    args layout.code outputMod (by rw [natural]; omega) (Or.inl (by rw [natural]; omega)) (by omega) normal
  have keptEntry := htrU64At_call_preserves_payload_requests state middle arguments (raw + inputOffset)
    (chunks + outputOffset) payload pointer length args entry layout.code outputMod
    (by rw [natural]; omega) (by rw [natural]; omega) (by omega) normal
  have globals := htrU64At_call_globals arguments state layout.code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_u64_at") arguments)
  have bounded := RunBounded.ofProg (ProgBounded.call htrU64At_funBounded (destination := none) arguments) layout.code (by omega)
  unfold RunBounded at bounded
  rw [normal] at globals metadata bounded
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_u64_at") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have spent : state.clock ≤ middle.clock + 30 := bounded.1
  have suffix := tail middle post sha accelerator zeroHashes chunk heap payload raw chunks out mark pointer length watched value
    (layout.transfer globals metadata.1)
    ⟨(keep _).trans locals.1,(keep _).trans locals.2.1,(keep _).trans locals.2.2.1,(keep _).trans locals.2.2.2⟩
    ((keep _).trans atMark) keptEntry small aligned fits before watchedBefore (by omega) rest
  exact suffix.trans frame

theorem payload_requests_suffix_memory : PayloadPostWithdrawalMemory 33 htrPayloadRequestsSuffixCost := by
  intro F state post sha accelerator zeroHashes chunk heap payload raw chunks out mark pointer length watched value
    layout locals atMark entry small aligned fits _ watchedBefore budget run
  exact htrPayload_requests_suffix_returned_memory state post sha accelerator zeroHashes chunk heap raw chunks out mark
    payload pointer length watched value layout locals.2.1 locals.2.2.1 locals.2.2.2 atMark locals.1 entry small
    aligned fits watchedBefore budget run

theorem payload_second_final_suffix_memory : PayloadPostWithdrawalMemory 32 htrPayloadSecondFinalCost :=
  payload_final_u64_memory_step 32 33 htrPayloadRequestsSuffixCost (520#64) (512#64) (by decide) (by decide)
    source_htrPayload_second_final_u64 payload_requests_suffix_memory

theorem payload_post_withdrawal_suffix_memory : PayloadPostWithdrawalMemory 31 htrPayloadPostWithdrawalCost :=
  payload_final_u64_memory_step 31 32 htrPayloadSecondFinalCost (512#64) (480#64) (by decide) (by decide)
    source_htrPayload_first_final_u64 payload_second_final_suffix_memory

#print axioms payload_final_u64_memory_step
#print axioms payload_requests_suffix_memory
#print axioms payload_second_final_suffix_memory
#print axioms payload_post_withdrawal_suffix_memory
end InitECandidate.Runtime
