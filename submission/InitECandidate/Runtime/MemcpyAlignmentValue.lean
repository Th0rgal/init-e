import InitECandidate.Runtime.MemcpyAlignedBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Typed pointer locals suffice to evaluate the real alignment guard. -/
theorem eval_memcpy_alignment_value {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source))) :
    ∃ flag : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) memcpyAlignmentCondition = some (.val (.word flag)) := by
  refine ⟨if Compiler.Encoders.Asm.wordCmpHOL .equal ((destination ||| source) &&& 7) 0 then 1 else 0,?_⟩
  simp [memcpyAlignmentCondition,evalHOLExact,evalListHOLExact,dstLocal,srcLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord]
  change (if Compiler.Encoders.Asm.wordCmpHOL .equal
    ((destination ||| (source ||| 0)) &&& ((7 : BitVec 64) &&& BitVec.allOnes 64)) 0 then (1 : BitVec 64) else 0) = _
  have zero : source ||| (0 : BitVec 64) = source := BitVec.or_zero
  rw [zero,BitVec.and_allOnes]
  rfl

#print axioms eval_memcpy_alignment_value
end InitECandidate.Runtime
