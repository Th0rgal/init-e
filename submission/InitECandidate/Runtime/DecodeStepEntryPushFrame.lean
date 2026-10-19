import InitECandidate.Runtime.DecodeStepKindPushFrame
import InitECandidate.Runtime.DecodeStepEntryPushProgress
import InitECandidate.Runtime.DecodeStepKindPushProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual stack push returned by the complete original decoder consumes
88 scratch bytes. The input parse, kind check, list conversion and both node
arities are connected through their actual continuation states. -/
theorem decode_step_entry_push_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array record : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepParseCost length.toNat + (decodeStepSlicesCost inputLimit + decodeStepListPushCost inputLimit) ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (run : evaluateHOLFiniteState s (decodeStepAt 0) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  have reached := decode_step_entry_parse_reaches s pointer length scratch frame ceiling inputLimit atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
  obtain ⟨ready,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s (decodeStepAt 0) (decodeStepAt 3)
    _ _ _ reached (by rw [run])
  obtain ⟨kind,pp,payload,atItem,parsedKind,payloadBound,_,ends,span,starts,globals,codeReady,domainReady,_⟩ := facts
  have limit : payload.toNat ≤ inputLimit := payloadBound.trans lengthBound
  have product : payload.toNat*((2*payload.toNat+1)*15+19) ≤ inputLimit*((2*inputLimit+1)*15+19) :=
    Nat.mul_le_mul limit (by omega)
  have slicesCost : decodeStepSlicesCost payload.toNat ≤ decodeStepSlicesCost inputLimit := by
    unfold decodeStepSlicesCost
    omega
  have beforeFrame : pp.toNat + payload.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pp.toNat) := by
    rcases inputBeforeFrame with before | ⟨aligned,after⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨aligned,by omega⟩
  cases tailRun : evaluateHOLFiniteState ready (decodeStepAt 3) with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    have progress := decode_step_kind_push_returned_frame ready output kind pp payload length scratch frame array record
      ceiling inputLimit atItem parsedKind span limit limitBound
      ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal) (codeReady.trans code)
      orderedFrame framePositive scratchBelow
      (by intro address lower upper; rw [domainReady]; exact arena address lower upper)
      (by omega) ((globals _).trans heap) arrayBound countLimit
      (by intro address lower upper; rw [domainReady]; exact heapArena address lower upper)
      beforeFrame (by omega) tailRun
    have finalGlobals := agreement.2.2.2.1
    rw [run,tailRun] at finalGlobals
    change post.globals = output.globals at finalGlobals
    rw [finalGlobals]
    exact progress

#print axioms decode_step_entry_push_returned_frame
end InitECandidate.Runtime
