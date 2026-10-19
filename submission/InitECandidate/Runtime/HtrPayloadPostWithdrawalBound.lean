import InitECandidate.Runtime.HtrPayloadRequestsSuffixBound
import InitECandidate.Runtime.HtrU64PayloadRequestsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def PayloadFinalLocals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload raw chunks out : BitVec 64) : Prop :=
  state.locals.lookup (ofString "pl") = some (.val (.word payload)) ∧
  state.locals.lookup (ofString "raw") = some (.val (.word raw)) ∧
  state.locals.lookup (ofString "ch") = some (.val (.word chunks)) ∧
  state.locals.lookup (ofString "out") = some (.val (.word out))

def PayloadPostWithdrawalBound (index cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (payload raw chunks out pointer length heap : BitVec 64),
    PayloadFinalLocals state payload raw chunks out → RlpSliceEntry state payload (4#64) pointer length →
    length.toNat ≤ 134217712 → chunks.toNat % 8 = 0 → chunks.toNat + 608 ≤ 33806089496 →
    payload.toNat + 72 < chunks.toNat →
    state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) → heap.toNat ≤ 33806089496 →
    state.code = originalRuntimeCode → cost ≤ state.clock → RunBounded state (htrPayloadAt index) cost

theorem payload_final_u64_step (index next cost : Nat) (inputOffset outputOffset : BitVec 64)
    (outputBound : outputOffset.toNat ≤ 576) (outputAligned : outputOffset.toNat % 8 = 0)
    (source : htrPayloadAt index = .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.op .add [.var .local (ofString "raw"),.const inputOffset],
       .op .add [.var .local (ofString "ch"),.const outputOffset]]) (htrPayloadAt next))
    (tail : PayloadPostWithdrawalBound next cost) : PayloadPostWithdrawalBound index (30 + cost) := by
  intro F state payload raw chunks out pointer length heap locals entry small aligned fits before atHeap heapFits code budget
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "raw"),.const inputOffset],
     .op .add [.var .local (ofString "ch"),.const outputOffset]]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word (raw + inputOffset)),.val (.word (chunks + outputOffset))] := by
    simp [arguments,evalListHOLExact,evalHOLExact,locals.2.1,locals.2.2.1,wordOpHOL,wordOp,valueIsWord,valueWord]
  have natural : (chunks + outputOffset).toNat = chunks.toNat + outputOffset.toNat := by
    apply BitVec.toNat_add_of_lt
    omega
  have outputMod : (chunks + outputOffset).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,aligned,outputAligned]
  rw [source]
  exact RunBounded.seq
    (RunBounded.ofProg (ProgBounded.call htrU64At_funBounded _ _) code (by omega)) budget (by
    intro post normal postCode remaining
    change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_u64_at") arguments) = (none,post) at normal
    have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
      have kept := evaluate_avoidsLocal_flowing key
        (.call (some (none,none)) (ofString "htr_u64_at") arguments) rfl state
        (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using kept
    have globals := htrU64At_call_globals arguments state code
    rw [normal] at globals
    have heapKept : post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := by
      rw [globals]
      exact atHeap
    have keptEntry := htrU64At_call_preserves_payload_requests state post arguments (raw + inputOffset)
      (chunks + outputOffset) payload pointer length args entry code outputMod
      (by rw [natural]; omega) (by rw [natural]; omega) (by omega) (by exact normal)
    exact tail post payload raw chunks out pointer length heap
      ⟨(keep _).trans locals.1,(keep _).trans locals.2.1,(keep _).trans locals.2.2.1,(keep _).trans locals.2.2.2⟩
      keptEntry small aligned fits before heapKept heapFits (postCode.trans code) remaining)

theorem source_htrPayload_second_final_u64 : htrPayloadAt 32 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.op .add [.var .local (ofString "raw"),.const 520],
       .op .add [.var .local (ofString "ch"),.const 512]]) (htrPayloadAt 33) := by rfl

theorem source_htrPayload_first_final_u64 : htrPayloadAt 31 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.op .add [.var .local (ofString "raw"),.const 512],
       .op .add [.var .local (ofString "ch"),.const 480]]) (htrPayloadAt 32) := by rfl

theorem payload_requests_suffix : PayloadPostWithdrawalBound 33 htrPayloadRequestsSuffixCost := by
  intro F state payload raw chunks out pointer length heap locals entry small _ _ _ atHeap heapFits code budget
  exact runBounded_htrPayload_requests_suffix state payload pointer length chunks out heap locals.1 locals.2.2.1
    locals.2.2.2 entry small atHeap heapFits code budget

def htrPayloadSecondFinalCost : Nat := 30 + htrPayloadRequestsSuffixCost

theorem payload_second_final_suffix : PayloadPostWithdrawalBound 32 htrPayloadSecondFinalCost :=
  payload_final_u64_step 32 33 htrPayloadRequestsSuffixCost (520#64) (512#64) (by decide) (by decide)
    source_htrPayload_second_final_u64 payload_requests_suffix

def htrPayloadPostWithdrawalCost : Nat := 30 + htrPayloadSecondFinalCost

theorem payload_post_withdrawal_suffix : PayloadPostWithdrawalBound 31 htrPayloadPostWithdrawalCost :=
  payload_final_u64_step 31 32 htrPayloadSecondFinalCost (512#64) (480#64) (by decide) (by decide)
    source_htrPayload_first_final_u64 payload_second_final_suffix

#print axioms payload_final_u64_step
#print axioms source_htrPayload_second_final_u64
#print axioms source_htrPayload_first_final_u64
#print axioms payload_requests_suffix
#print axioms payload_second_final_suffix
#print axioms payload_post_withdrawal_suffix
end InitECandidate.Runtime
