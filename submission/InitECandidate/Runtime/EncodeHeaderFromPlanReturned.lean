import InitECandidate.Runtime.EncodeHeaderFinalReturned
import InitECandidate.Runtime.EncodeHeaderActualPrefixPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- All real fixed/variable writers and the optional header fields deliver the
bounded original final return. -/
theorem encode_header_from_plan_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (header heap lo length buffer : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo (header+136) length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : (header+136).toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (atBuf : s.locals.lookup (ofString "buf")=some (.val (.word buffer))) (bufferLow : 8≤buffer.toNat)
 (cursorLow : EncodeHeaderCursorLower s (buffer.toNat+9))
 (run : evaluateHOLFiniteState s (encodeHeaderAt 4)=(some (.returned value),post)) :
 ∃start encodedLength : BitVec 64,value=.rStruct [.val (.word start),.val (.word encodedLength)] ∧
 buffer.toNat≤start.toNat ∧encodedLength.toNat≤DF := by
 rw [source_encode_header_actual_prefix_plan] at run
 obtain ⟨variableState,variableRun,variableValid,variableBuf,variableMoves⟩:=encode_header_prefix_plan_returned
  encodeHeaderActualPrefixItems (encodeHeaderAt 26) s post value header heap lo (header+136) length DF
  valid cap heapCap heapFence aligned below loHeap run
 obtain ⟨fixedState,fixedRun,fixedValid,fixedBuf,fixedMoves⟩:=encode_header_variable_returned variableState post value
  header heap lo length DF variableValid cap heapCap heapFence aligned below loHeap variableRun
 obtain ⟨finalState,finalRun,finalValid,finalBuf,finalMoves⟩:=encode_header_fixed_returned fixedState post value
  header heap lo length DF fixedValid cap heapCap heapFence aligned below loHeap fixedRun
 obtain ⟨cursor,atP,_,high⟩:=finalValid.cursor
 have finalBuffer : finalState.locals.lookup (ofString "buf")=some (.val (.word buffer)) :=
  finalBuf.trans (fixedBuf.trans (variableBuf.trans atBuf))
 have lower:=finalMoves _ (fixedMoves _ (variableMoves _ cursorLow)) cursor atP
 obtain ⟨start,encodedLength,result,startLow,_,encodedSmall⟩:=encode_header_final_returned finalState post value cursor buffer DF
  finalValid.code finalValid.fence cap atP finalBuffer bufferLow lower high finalRun
 exact ⟨start,encodedLength,result,startLow,encodedSmall⟩
#print axioms encode_header_from_plan_returned
end InitECandidate.Runtime
