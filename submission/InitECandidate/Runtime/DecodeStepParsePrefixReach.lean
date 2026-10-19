import InitECandidate.Runtime.DecodeStepParseCallBound
import InitECandidate.Runtime.StateInitJournalSource
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanLocalCallHandlerNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepAt (n : Nat) : ProgHOL 64 :=
  stateInitSpineDrop n (sourceFunctionBody Guest.guestFn__decode_step)

theorem source_decode_step_parse_sequence : decodeStepAt 2 =
    .seq decodeStepParseCall (decodeStepAt 3) := by
  simp only [decodeStepAt,decodeStepParseCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original parser sequence reaches its actual kind dispatch with a bounded
payload and restored scratch globals, or terminates in the proved call budget. -/
theorem decode_step_parse_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : decodeStepParseCost length.toNat ≤ s.clock) :
    Reaches s (decodeStepAt 2)
      (fun post => ∃ kind payloadPointer payload : BitVec 64,
        post.locals.lookup (ofString "it") =
          some (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word length)]) ∧
        (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
        payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
        payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
        (∀ watched, post.globals.lookup watched = s.globals.lookup watched) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be)
      (decodeStepParseCost length.toNat) (decodeStepAt 3) := by
  rw [source_decode_step_parse_sequence]
  apply runBounded_seq_reaches s decodeStepParseCall (decodeStepAt 3) _ (decodeStepParseCost length.toNat)
    (runBounded_decode_step_parse_call s pointer length scratch frame ceiling inputLimit atPointer atLength
      inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget)
  · intro value equal
    have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "p"),.var .local (ofString "n")] =
        some [.val (.word pointer),.val (.word length)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact,evalHOLExact,atPointer,atLength]
    have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_decode_fully")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_decode_fully)
      (.comb [.one,.one,.one,.one]) pointer length (by decide)
      (by rw [code]; exact originalRuntimeCode_rlpDecodeFully_lookup)
    have returned : evaluateHOLFiniteState s decodeStepParseCall =
        (some (.returned value),(evaluateHOLFiniteState s decodeStepParseCall).2) := Prod.ext equal rfl
    rw [source_decode_step_parse_call] at returned
    exact evaluate_localCall_handler_no_return s _ (ofString "it") (ofString "rlp_decode_fully")
      (.comb [.one,.one,.one,.one]) _ _ (sourceFunctionBody Guest.guestFn_rlp_decode_fully)
      (.call (some (none,none)) (ofString "mpt_fail") [.const 3]) (ofString "RlpErr") (ofString "e")
      (rlpHeaderCallee pointer length) args lookup value
      (fun current => evaluate_noDirectReturn _ rfl current value) returned
  · intro post normal
    obtain ⟨kind,payloadPointer,payload,atItem,flag,small,positive,ends,nowrap,starts,globals⟩ :=
      decode_step_parse_call_normal_contract s post pointer length scratch frame ceiling inputLimit atPointer atLength
        inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
        (by unfold decodeStepParseCost at budget; omega) normal
    have metadata := evaluateHOLFiniteState_metadata s decodeStepParseCall
    rw [normal] at metadata
    exact ⟨kind,payloadPointer,payload,atItem,flag,small,positive,ends,nowrap,starts,globals,
      metadata.1,metadata.2.1,metadata.2.2.1⟩

#print axioms source_decode_step_parse_sequence
#print axioms decode_step_parse_prefix_reaches
end InitECandidate.Runtime
