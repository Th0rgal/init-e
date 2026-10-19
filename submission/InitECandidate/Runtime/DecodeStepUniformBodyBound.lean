import InitECandidate.Runtime.DecodeStepKindUniformBound
import InitECandidate.Runtime.DecodeStepEntryParseReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def decodeStepBodyCost (limit : Nat) : Nat :=
  decodeStepParseCost limit + (decodeStepSlicesCost limit + decodeStepTwoCaseCost limit)

theorem decodeStepParseCost_mono (n m : Nat) (h : n ≤ m) : decodeStepParseCost n ≤ decodeStepParseCost m := by
  exact Nat.add_le_add_right (Nat.mul_le_mul h (by omega)) _

theorem decodeStepSlicesCost_mono (n m : Nat) (h : n ≤ m) : decodeStepSlicesCost n ≤ decodeStepSlicesCost m := by
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul h (by omega)) (Nat.mul_le_mul_right 12 h)) _

/-- The complete frozen original decoder has a uniform input-dependent source
clock bound. Every parsed kind and supported/unsupported node arity, memory
failure and allocation rejection is covered; no successful heap reserve is assumed. -/
theorem runBounded_decode_step_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) :
    RunBounded s (sourceFunctionBody Guest.guestFn__decode_step) (decodeStepBodyCost inputLimit) := by
  change RunBounded s (decodeStepAt 0) (decodeStepBodyCost inputLimit)
  have parseMono := decodeStepParseCost_mono length.toNat inputLimit lengthBound
  have actualBudget : decodeStepParseCost length.toNat +
      (decodeStepSlicesCost inputLimit + decodeStepTwoCaseCost inputLimit) ≤ s.clock :=
    (Nat.add_le_add_right parseMono _).trans budget
  have reached := decode_step_entry_parse_reaches s pointer length scratch frame ceiling inputLimit atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    ((Nat.le_add_right _ _).trans actualBudget)
  have whole := RunBounded.ofReaches actualBudget reached (by
    intro ready facts ticks
    obtain ⟨kind,pp,payload,atItem,parsedKind,payloadBound,_,ends,span,starts,globals,codeReady,domainReady,_⟩ := facts
    have limit : payload.toNat ≤ inputLimit := payloadBound.trans lengthBound
    have sliceMono := decodeStepSlicesCost_mono payload.toNat inputLimit limit
    have beforeFrame : pp.toNat + payload.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pp.toNat) := by
      rcases inputBeforeFrame with before | ⟨aligned,after⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨aligned,by omega⟩
    have bounded := runBounded_decode_step_kind ready kind pp payload length scratch frame array ceiling inputLimit
      atItem parsedKind span limit limitBound ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal)
      (codeReady.trans code) orderedFrame framePositive scratchBelow
      (by intro address lower upper; rw [domainReady]; exact arena address lower upper)
      ((Nat.add_le_add_right sliceMono _).trans ticks) ((globals _).trans heap) arrayBound countLimit
      (by intro address lower upper; rw [domainReady]; exact heapArena address lower upper)
      beforeFrame (by omega) arrayAbove limitCap
    exact bounded.weaken (Nat.add_le_add_right sliceMono _))
  exact whole.weaken (Nat.add_le_add_right parseMono _)

#print axioms decodeStepParseCost_mono
#print axioms decodeStepSlicesCost_mono
#print axioms runBounded_decode_step_body
end InitECandidate.Runtime
