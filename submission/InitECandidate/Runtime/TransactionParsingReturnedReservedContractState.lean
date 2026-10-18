import InitECandidate.Runtime.TransactionTypeParseReturnedReservedContract
import InitECandidate.Runtime.TransactionParsingScopesInitializedState
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_parsing_returned_reserved_contract_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (byte : BitVec 64)
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word byte)))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 6) = (some (.returned value),post)) :
    ∃ (middle output : PanSemStateFiniteExact 64 F) (tag payloadPointer payload total kind : BitVec 64),
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),output) ∧
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
      reserve ≤ middle.clock ∧ middle.clock ≤ state.clock ∧ (post.memory = output.memory ∧ post.globals = output.globals) := by
  obtain ⟨entry,output,bodyRun,memory,globals,entryCode,domain,clock,locals,atType,atCount,finalMemory⟩ :=
    transaction_parsing_scopes_returned_initialized_state state post value run
  have retained : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro index inside
    obtain ⟨pointer,length,item⟩ := valid index inside
    exact ⟨pointer,length,RlpSliceInputEntry.after_frame state entry array index pointer length input inputLength item domain
      (by rw [memory]) (by rw [memory])⟩
  obtain ⟨middle,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,ends,noWrap,starts,
      finalGlobals,finalCode,finalDomain,atTx,supported,typePost,countPost,available,remaining⟩ :=
    transaction_type_parse_returned_reserved_contract entry output pointer length scratch frame ceiling inputLimit
      ((locals _ (by decide) (by decide) (by decide)).trans pointerLocal)
      ((locals _ (by decide) (by decide) (by decide)).trans lengthLocal)
      positive inputRange lengthBound limitBound
      (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
      (entryCode.trans code) orderedFrame framePositive scratchBelow
      (by intro address low high; rw [domain]; exact arena address low high)
      reserve (by rw [clock]; exact budget) array count input inputLength retained before
      tx ((locals _ (by decide) (by decide) (by decide)).trans txLocal)
      byte atType ((locals _ (by decide) (by decide) (by decide)).trans byteLocal) atCount value bodyRun
  refine ⟨middle,output,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,
    ends,noWrap,starts,finalGlobals.trans globals,finalCode.trans entryCode,finalDomain.trans domain,atTx,supported,
    typePost,countPost,available,?_,finalMemory⟩
  rw [clock] at remaining
  exact remaining

#print axioms transaction_parsing_returned_reserved_contract_state
end InitECandidate.Runtime
