import InitECandidate.Runtime.TransactionTypeParseReturnedHeapPrefix
import InitECandidate.Runtime.TransactionTypeBranchTopContract
import InitECandidate.Runtime.TransactionTypeBranchLocals
import InitECandidate.Runtime.TransactionTypeBranchBound
import InitECandidate.Runtime.NormalLocalFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem parser_reserve_of_cost (clock remaining cost reserve : Nat)
    (budget : cost + reserve ≤ clock) (spent : clock ≤ remaining + cost) : reserve ≤ remaining := by omega

theorem transaction_type_parse_returned_heap_reserved_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (reserve : Nat)
    (budget : (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + reserve ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (above : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (byte : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word (0 : BitVec 64))))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word byte)))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 9) = (some (.returned value),post)) :
    ∃ (middle : PanSemStateFiniteExact 64 F) (tag payloadPointer payload total kind : BitVec 64),
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      middle.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word payloadPointer),.val (.word payload),.val (.word total)]) ∧
      (tag = 0 ∨ tag = 1) ∧ payload.toNat ≤ length.toNat ∧ total.toNat ≤ length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      middle.globals = state.globals ∧ middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧
      middle.locals.lookup (ofString "tx") = some (.val (.word tx)) ∧
      (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      middle.locals.lookup (ofString "t") = some (.val (.word kind)) ∧
      middle.locals.lookup (ofString "nfields") = some (.val (.word (BitVec.ofNat 64 (transactionRequiredFields kind)))) ∧
      reserve ≤ middle.clock ∧ middle.clock ≤ state.clock := by
  have ticks : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635 ≤ state.clock :=
    Nat.le_trans (Nat.le_add_right _ _) budget
  have enough : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock :=
    Nat.le_trans (Nat.add_le_add_left (by decide : 92634 ≤ 92635) _) ticks
  obtain ⟨middle,parsed,tail,retained⟩ := transaction_type_parse_returned_heap_input_prefix state post pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena enough array count input inputLength valid fits above value run
  obtain ⟨tag,payloadPointer,payload,total,atTop,tagBound,payloadBound,totalBound,ends,noWrap,starts,globals⟩ :=
    transaction_type_branch_normal_top_contract state middle pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena enough parsed
  have metadata := evaluateHOLFiniteState_metadata state transactionTypeParseBranch
  rw [parsed] at metadata
  have txFrame := evaluate_normalLocalFrame (ofString "tx") transactionTypeParseBranch (by
    simp only [transactionTypeParseBranch,transactionAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl) state middle parsed
  obtain ⟨kind,supported,typePost,countPost⟩ := transaction_type_branch_normal_type_count state middle byte typeLocal byteLocal countLocal parsed
  have bounded := transaction_type_branch_bounded state pointer length scratch frame ceiling inputLimit
    pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks
  rw [parsed] at bounded
  dsimp only at bounded
  have available := parser_reserve_of_cost state.clock middle.clock _ reserve budget bounded.1
  exact ⟨middle,tag,payloadPointer,payload,total,kind,tail,retained,atTop,tagBound,payloadBound,totalBound,
    ends,noWrap,starts,globals,metadata.1,metadata.2.1,txFrame.trans txLocal,supported,typePost,countPost,available,bounded.2.1⟩

#print axioms transaction_type_parse_returned_heap_reserved_contract
end InitECandidate.Runtime
