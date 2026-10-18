import InitECandidate.Runtime.StoreLEBounds
import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.PanSeqByteStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def serializeResultCopy : ProgHOL 64 :=
  .call (some (none,none)) (ofString "memcpy")
    [.var .local (ofString "out"),.var .local (ofString "root"),.const 32]
def serializeResultSuccess : ProgHOL 64 :=
  .storeByte (.op .add [.var .local (ofString "out"),.const 32]) (.var .local (ofString "succ"))
def serializeResultChain : ProgHOL 64 :=
  .call (some (none,none)) (ofString "st_le64")
    [.op .add [.var .local (ofString "out"),.const 33],.var .local (ofString "chain_id")]
def serializeResultTail : ProgHOL 64 :=
  .seq (.storeByte (.op .add [.var .local (ofString "out"),.const 41])
    (.op .and [.var .local (ofString "schema_id"),.const 255]))
    (.seq (.storeByte (.op .add [.var .local (ofString "out"),.const 42])
      (.shift .lsr (.var .local (ofString "schema_id")) (.const 8))) (.return (.const 43)))

theorem source_serializeResult_body : sourceFunctionBody Guest.guestFn_serialize_result =
    .seq serializeResultCopy (.seq serializeResultSuccess (.seq serializeResultChain serializeResultTail)) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Serializing either a successful result or a decoder rejection uses at
most 19 source clocks, including inaccessible input/output memory. -/
theorem evaluate_serializeResult_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (output root : BitVec 64)
    (atOutput : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (atRoot : state.locals.lookup (ofString "root") = some (.val (.word root)))
    (code : state.code = originalRuntimeCode) (budget : 19 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_serialize_result)
    state.clock ≤ evaluated.2.clock + 19 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "out"),.var .local (ofString "root"),.const 32] =
        some [.val (.word output),.val (.word root),.val (.word 32)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atOutput,atRoot]
  have copy := evaluate_memcpy_call_bounded state _ output root 32 arguments code (by decide)
    (by change 16 ≤ state.clock; omega)
  change state.clock ≤ (evaluateHOLFiniteState state serializeResultCopy).2.clock + 16 ∧
    (evaluateHOLFiniteState state serializeResultCopy).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state serializeResultCopy).1 ≠ some .timeOut at copy
  rw [source_serializeResult_body]
  apply evaluate_sequence_code_bounded state _ _ 16 3 copy ?_ budget
  intro next kept enough
  have zero := clockPreserving_of_byteStraightLine serializeResultSuccess (by rfl) next
  have safe := evaluate_byteStraightLine_no_timeout serializeResultSuccess (by rfl) next
  apply evaluate_sequence_code_bounded next serializeResultSuccess _ 0 3
    ⟨by rw [zero]; omega,by rw [zero],safe⟩ ?_ (by omega)
  intro current installed fuel
  exact evaluate_sequence_byteStraight_bounded current serializeResultChain serializeResultTail 3
    (evaluate_storeLE64_call_bounded current none _ (installed.trans (kept.trans code)) fuel) (by rfl)

#print axioms evaluate_serializeResult_body_bounded
end InitECandidate.Runtime
