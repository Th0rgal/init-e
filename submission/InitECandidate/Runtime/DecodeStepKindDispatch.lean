import InitECandidate.Runtime.DecodeStepEntryParseReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepKindGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0))
    (.seq (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0))
      (.return (.rstruct [.const 0,.const 0])) .skip)
      (.call (some (none,none)) (ofString "mpt_fail") [.const 4])) .skip

theorem source_decode_step_kind_dispatch : decodeStepAt 3 =
    .seq decodeStepKindGuard (decodeStepAt 4) := by
  simp only [decodeStepAt,decodeStepKindGuard,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A real parsed list proceeds to slice construction in exactly the same state. -/
theorem evaluate_decode_step_list_dispatch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer payload consumed : BitVec 64)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word payload),.val (.word consumed)])) :
    evaluateHOLFiniteState s (decodeStepAt 3) = evaluateHOLFiniteState s (decodeStepAt 4) := by
  rw [source_decode_step_kind_dispatch,evaluateHOLFiniteState_seq_line780]
  simp [decodeStepKindGuard,evaluateHOLFiniteState_ite,evalHOLExact,atItem,
    Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

/-- The original empty byte-string branch returns a completed empty node with
no allocation or source clock spent. It must not be counted as a stack push. -/
theorem evaluate_decode_step_empty_bytes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer consumed : BitVec 64)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (0#64)),.val (.word pointer),.val (.word (0#64)),.val (.word consumed)])) :
    evaluateHOLFiniteState s (decodeStepAt 3) =
      (some (.returned (.rStruct [.val (.word (0#64)),.val (.word (0#64))])),emptyLocalsHOLFinite s) := by
  rw [source_decode_step_kind_dispatch,evaluateHOLFiniteState_seq_line780]
  simp [decodeStepKindGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_seq_line780,evalHOLExact,
    evalListHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,
    evaluateHOLFiniteState_skip,shapeOfHOLExact]

#print axioms source_decode_step_kind_dispatch
#print axioms evaluate_decode_step_list_dispatch
#print axioms evaluate_decode_step_empty_bytes
end InitECandidate.Runtime
