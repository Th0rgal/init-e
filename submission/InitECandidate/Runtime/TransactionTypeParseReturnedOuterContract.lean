import InitECandidate.Runtime.TransactionTypeParseReturnedPrefix
import InitECandidate.Runtime.TransactionTypeBranchTopContract
import InitECandidate.Runtime.NormalLocalFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_parse_returned_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 9) = (some (.returned value),post)) :
    ∃ (middle : PanSemStateFiniteExact 64 F) (tag payloadPointer payload total : BitVec 64),
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      middle.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word payloadPointer),.val (.word payload),.val (.word total)]) ∧
      (tag = 0 ∨ tag = 1) ∧ payload.toNat ≤ length.toNat ∧ total.toNat ≤ length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      middle.globals = state.globals ∧ middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      middle.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
  obtain ⟨middle,parsed,tail,retained⟩ := transaction_type_parse_returned_input_prefix state post pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena budget array count input inputLength valid before value run
  obtain ⟨tag,payloadPointer,payload,total,atTop,tagBound,payloadBound,totalBound,ends,noWrap,starts,globals⟩ :=
    transaction_type_branch_normal_top_contract state middle pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget parsed
  have metadata := evaluateHOLFiniteState_metadata state transactionTypeParseBranch
  rw [parsed] at metadata
  have txFrame := evaluate_normalLocalFrame (ofString "tx") transactionTypeParseBranch (by
    simp only [transactionTypeParseBranch,transactionAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl) state middle parsed
  exact ⟨middle,tag,payloadPointer,payload,total,tail,retained,atTop,tagBound,payloadBound,totalBound,
    ends,noWrap,starts,globals,metadata.1,metadata.2.1,txFrame.trans txLocal⟩

#print axioms transaction_type_parse_returned_outer_contract
end InitECandidate.Runtime
