import InitECandidate.Runtime.RlpDecodeFullyLocalCallRuntimeContract
import InitECandidate.Runtime.PanLocalCallCodeTerminalHandlerNormal
import InitECandidate.Runtime.MptFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def decodeStepParseCall : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn__decode_step with
  | .dec _ _ _ (.dec _ _ _ (.seq call _)) => call
  | _ => .skip

theorem source_decode_step_parse_call : decodeStepParseCall =
    .call (some (some (.local,ofString "it"),some (ofString "RlpErr",ofString "e",
      .call (some (none,none)) (ofString "mpt_fail") [.const 3])))
      (ofString "rlp_decode_fully") [.var .local (ofString "p"),.var .local (ofString "n")] := by
  simp only [decodeStepParseCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Normal completion of the original handled parser call restores all globals
(including the scratch frontier) and produces a bounded RLP payload. The MPT
error handler cannot manufacture a normal return. -/
theorem decode_step_parse_call_normal_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepParseCall = (none,post)) :
    ∃ kind payloadPointer payload : BitVec 64,
      post.locals.lookup (ofString "it") =
        some (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word length)]) ∧
      (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      (∀ watched, post.globals.lookup watched = s.globals.lookup watched) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),.var .local (ofString "n")] =
      some [.val (.word pointer),.val (.word length)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atPointer,atLength]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_decode_fully")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_decode_fully)
    (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpDecodeFully_lookup)
  rw [source_decode_step_parse_call] at run
  have normal := evaluate_localCall_code_terminal_handler_normal_result s post (ofString "it")
    (ofString "rlp_decode_fully") (.comb [.one,.one,.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_rlp_decode_fully)
    (.call (some (none,none)) (ofString "mpt_fail") [.const 3]) (ofString "RlpErr") (ofString "e")
    (rlpHeaderCallee pointer length) args lookup
    (by
      intro current installed
      exact evaluate_mptFail_call_terminal current (.const 3) 3 (installed.trans code)
        (by rw [evalListHOLFinite_eq_toExact]; rfl)) run
  exact rlpDecodeFully_local_call_runtime_contract s post (ofString "it") _ pointer length scratch frame ceiling
    inputLimit args inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena budget normal

#print axioms source_decode_step_parse_call
#print axioms decode_step_parse_call_normal_contract
end InitECandidate.Runtime
