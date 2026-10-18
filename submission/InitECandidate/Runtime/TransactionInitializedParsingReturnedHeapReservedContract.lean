import InitECandidate.Runtime.TransactionParsingReturnedHeapReservedContract
import InitECandidate.Runtime.TransactionInitializationSource
import InitECandidate.Runtime.TransactionInitializationRuntimeFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem initialized_parser_reserve (clock remaining reserved : Nat)
    (budget : 401 + reserved ≤ clock) (cost : clock ≤ remaining + 401) : reserved ≤ remaining := by omega

theorem transaction_initialized_parsing_returned_heap_reserved_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : 401 + ((length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) + reserve) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (above : ceiling ≤ array.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (byte : BitVec 64)
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word byte)))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 3) = (some (.returned value),post)) :
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
      reserve ≤ middle.clock ∧ middle.clock ≤ state.clock ∧ post.memory = output.memory := by
  have ticks : 401 ≤ state.clock := Nat.le_trans (Nat.le_add_right _ _) budget
  obtain ⟨initialized,initialRun,bodyRun,retained⟩ := transaction_initialization_returned_input_prefix state post
    tx pointer length array count input inputLength txLocal pointerLocal lengthLocal code ticks small aligned txArena valid beforeTx value run
  have transport := transaction_record_initialization_runtime_frame state tx txLocal code ticks small aligned txArena
  rw [initialRun] at transport
  dsimp only at transport
  obtain ⟨cost,initRemaining,_,locals,globals,initCode,domain⟩ := transport
  obtain ⟨middle,output,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,ends,noWrap,starts,
      finalGlobals,finalCode,finalDomain,atTx,supported,typePost,countPost,available,remaining,finalMemory⟩ :=
    transaction_parsing_returned_heap_reserved_contract initialized post pointer length scratch frame ceiling inputLimit
      (by rw [locals]; exact pointerLocal) (by rw [locals]; exact lengthLocal)
      positive inputRange lengthBound limitBound
      (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
      (initCode.trans code) orderedFrame framePositive scratchBelow
      (by intro address low high; rw [domain]; exact arena address low high)
      reserve (initialized_parser_reserve _ _ _ budget cost) array count input inputLength retained fits above
      tx (by rw [locals]; exact txLocal) byte (by rw [locals]; exact byteLocal) value bodyRun
  exact ⟨middle,output,tag,payloadPointer,payload,total,kind,tail,preserved,atTop,tagBound,payloadBound,totalBound,
    ends,noWrap,starts,finalGlobals.trans globals,finalCode.trans initCode,finalDomain.trans domain,atTx,supported,
    typePost,countPost,available,Nat.le_trans remaining initRemaining,finalMemory⟩

#print axioms transaction_initialized_parsing_returned_heap_reserved_contract
end InitECandidate.Runtime
