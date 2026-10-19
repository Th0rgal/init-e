import InitECandidate.Runtime.DecodeStepKindUniformBound
import InitECandidate.Runtime.DecodeStepSlicesTableMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_kind_push_returned_table {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame array originalPointer originalLength : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word originalPointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word originalLength)))
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (parsedKind : kind = 0 ∨ kind = 1)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat + decodeStepTwoCaseCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) (record : BitVec 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 3) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    DecoderPushedTable post record originalPointer originalLength pointer length ceiling := by
  rcases parsedKind with zero | list
  · subst kind
    by_cases empty : length = 0
    · subst length
      rw [evaluate_decode_step_empty_bytes s pointer consumed atItem] at run
      have values := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)
      have words := (List.cons.inj (ValueHOL.rStruct.inj values)).1
      have impossible : (0#64) = (1 : BitVec 64) := HolWordLab.word.inj (ValueHOL.val.inj words)
      exact False.elim ((by decide : (0#64) ≠ (1 : BitVec 64)) impossible)
    · rw [evaluate_decode_step_nonempty_bytes s pointer length consumed empty code atItem] at run
      exact False.elim (evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4] _ (congrArg Prod.fst run))
  · subst kind
    rw [evaluate_decode_step_list_dispatch s pointer length consumed atItem] at run
    exact decode_step_slices_push_returned_table s post pointer length consumed scratch frame array originalPointer originalLength ceiling inputLimit
      atPointer atLength atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      budget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap record run

#print axioms decode_step_kind_push_returned_table
end InitECandidate.Runtime
