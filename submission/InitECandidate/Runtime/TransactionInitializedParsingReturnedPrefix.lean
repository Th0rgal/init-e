import InitECandidate.Runtime.TransactionParsingReturnedPrefix
import InitECandidate.Runtime.TransactionInitializationSource
import InitECandidate.Runtime.TransactionInitializationRuntimeFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_initialized_parsing_returned_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
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
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (small : tx.toNat + 400 ≤ 33806089496) (aligned : tx.toNat % 8 = 0)
    (txArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < tx.toNat + 400 → state.memaddrs address)
    (budget : 401 + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634) ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (beforeTx : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 3) = (some (.returned value),post)) :
    ∃ middle output : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),output) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧ post.memory = output.memory := by
  have ticks : 401 ≤ state.clock := by omega
  obtain ⟨initialized,initialRun,tail,retained⟩ := transaction_initialization_returned_input_prefix state post
    tx pointer length array count input inputLength txLocal pointerLocal lengthLocal code ticks small aligned txArena valid beforeTx value run
  have transport := transaction_record_initialization_runtime_frame state tx txLocal code ticks small aligned txArena
  rw [initialRun] at transport
  dsimp only at transport
  obtain ⟨cost,_,_,locals,globals,postCode,domain⟩ := transport
  exact transaction_parsing_returned_input_prefix initialized post pointer length scratch frame ceiling inputLimit
    (by rw [locals]; exact pointerLocal) (by rw [locals]; exact lengthLocal)
    positive inputRange lengthBound limitBound
    (by rw [globals]; exact scratchGlobal) (by rw [globals]; exact frameGlobal)
    (postCode.trans code) orderedFrame framePositive scratchBelow
    (by intro address low high; rw [domain]; exact arena address low high)
    (by
      apply Nat.le_of_add_le_add_right (b := 401)
      simpa only [Nat.add_comm 401] using Nat.le_trans budget cost) array count input inputLength retained before value tail

#print axioms transaction_initialized_parsing_returned_input_prefix
end InitECandidate.Runtime
