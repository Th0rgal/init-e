import InitECandidate.Runtime.HeaderNumericFieldCallFrame
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual assignment calls consume the real slice entry and reach the next
statement with checked output and preserved workspace/table memory, or terminate. -/
theorem header_numeric_field_assignment_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (field : HeaderNumericField)
    (array index extra pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some (headerNumericFieldValues field array index extra))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock)
 :
    Reaches s (.seq (.call (some (some (.local,name),none)) (headerNumericFieldName field) arguments) continuation)
      (fun post => ∃ value : ValueHOL 64, post.locals = s.locals.update (name,value) ∧
        shapeEqHOL (shapeOfHOLExact value) (headerNumericFieldShape field) = true ∧
        post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ global : MlS, post.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → post.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) continuation := by
  have bounded := runBounded_header_numeric_field_call s field array index extra pointer length input inputLength scratch frame
    ceiling inputLimit (some (.local,name)) arguments args entry inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena budget
  apply runBounded_seq_reaches s _ continuation _ (headerRlpFieldCost inputLimit + 35) bounded
  · intro value
    exact evaluate_noDirectReturn _ rfl s value
  · intro post normal
    exact header_numeric_field_call_normal_frame s post field array index extra pointer length input inputLength scratch frame
      ceiling inputLimit name arguments args entry inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena budget normal

#print axioms header_numeric_field_assignment_reaches
end InitECandidate.Runtime
