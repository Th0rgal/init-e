import InitECandidate.Runtime.DecodeHeaderCountGuard
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.RlpDecodeFullyBodyBound
import InitECandidate.Runtime.RlpDecodeFullyBodyRuntimeContract
import InitECandidate.Runtime.RlpDecodeFullyBodyAbove
import InitECandidate.Runtime.OriginalRlpDecodeFullyCode
import InitECandidate.Runtime.HeaderRlpFieldInputBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def decodeHeaderRlpCost (limit : Nat) : Nat := headerRlpFieldCost limit + 2

theorem source_decode_header_rlp : decodeHeaderAt 0 =
    .decCall (ofString "top") (.comb [.one,.one,.one,.one]) (ofString "rlp_decode_fully")
      [.var .local (ofString "p"),.var .local (ofString "len")] (decodeHeaderAt 1) := rfl

/-- Header decoding's real initial full RLP parse reaches the kind check with
execution-derived bounded payload fields and restored workspace, or terminates. -/
theorem decode_header_rlp_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeHeaderRlpCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 0)
      (fun ready => ∃ kind input size : BitVec 64,
        (kind = 0 ∨ kind = 1) ∧ size.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
        pointer.toNat ≤ input.toNat ∧ input.toNat + size.toNat ≤ pointer.toNat + length.toNat ∧
        input.toNat + size.toNat < 2^64 ∧
        ready.locals = s.locals.update (ofString "top",
          .rStruct [.val (.word kind),.val (.word input),.val (.word size),.val (.word length)]) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ name : MlS, ready.globals.lookup name = s.globals.lookup name) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → ready.memory address = s.memory address))
      (decodeHeaderRlpCost inputLimit) (decodeHeaderAt 1) := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite s callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),.var .local (ofString "len")] = some [.val (.word pointer),.val (.word length)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atPointer,atLength]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_decode_fully") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_decode_fully) (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpDecodeFully_lookup)
  have product := Nat.mul_le_mul lengthBound (by omega : (2 * length.toNat + 1) * 15 + 19 ≤ (2 * inputLimit + 1) * 15 + 19)
  have bodyBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ entry.clock := by
    change _ ≤ s.clock - 1
    unfold decodeHeaderRlpCost headerRlpFieldCost at budget
    omega
  have bounded := evaluate_rlpDecodeFully_body_bounded entry pointer length scratch frame ceiling inputLimit p len noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget
  rw [source_decode_header_rlp]
  change Reaches s _ _ ((headerRlpFieldCost inputLimit + 1) + 1) _
  apply bounded_decCall_reaches s _ _ _ _ _ _ _ _ callee (headerRlpFieldCost inputLimit + 1) _ args lookup (by exact budget)
    ((show RunBounded entry (sourceFunctionBody Guest.guestFn_rlp_decode_fully)
      (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634) from bounded).weaken (by unfold headerRlpFieldCost; omega))
  intro value post returned _
  obtain ⟨kind,input,size,valueEq,kindBound,sizeBound,positive,ends,fit,starts,globals⟩ :=
    rlpDecodeFully_body_returned_runtime_contract entry post pointer length scratch frame ceiling inputLimit p len noWrap lengthBound
      limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega) value returned
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_decode_fully)
  rw [returned] at metadata
  refine ⟨kind,input,size,kindBound,sizeBound,positive,starts,ends,fit,?_,metadata.2.1,metadata.1,globals,?_⟩
  · change s.locals.update (ofString "top",value) = _
    rw [valueEq]
  · intro address above
    exact rlpDecodeFully_body_returned_above entry post pointer length scratch frame ceiling inputLimit p len noWrap lengthBound
      limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega) value returned address above

#print axioms source_decode_header_rlp
#print axioms decode_header_rlp_entry_reaches
end InitECandidate.Runtime
