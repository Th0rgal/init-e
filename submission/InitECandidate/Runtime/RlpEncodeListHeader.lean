import InitECandidate.Runtime.RlpEncodeBytesTail
import InitECandidate.Runtime.RlpHeaderLenMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The installed body of `rlp_encode_list_header`: one tail call of the actual
`rlp_write_header` with the list type byte `0xc0 = 192` as its base. -/
def rlpEncodeListHeader : ProgHOL 64 :=
  .call none (ofString "rlp_write_header")
    [.var .local (ofString "dst"), .const (192#64), .var .local (ofString "payload_len")]

/-- The body equation of the actual `rlp_encode_list_header`. -/
theorem source_rlpEncodeListHeader_body :
    sourceFunctionBody Guest.guestFn_rlp_encode_list_header = rlpEncodeListHeader := by
  rw [rlpEncodeListHeader]
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpEncodeListHeader_body

/-- **The actual `rlp_encode_list_header`** writes only inside the nine-byte window at `dst`: it is
one tail call of the actual `rlp_write_header` with base `0xc0`. -/
theorem rlpEncodeListHeader_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D N w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup (ofString "payload_len") = some (.val (.word N)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_list_header)).2.memory w =
      s.memory w := by
  rw [source_rlpEncodeListHeader_body]
  have argsEval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "dst"), .const (192#64), .var .local (ofString "payload_len")] =
      some [.val (.word D), .val (.word 192), .val (.word N)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,hd,hn]
  obtain ⟨callee,look⟩ := lookupCodeHOLFinite_of_exact s.code.lookup (ofString "rlp_write_header")
    [.val (.word D), .val (.word 192), .val (.word N)]
    (sourceFunctionBody Guest.guestFn_rlp_write_header) _ .one
    (by rw [code]; exact rlpWriteHeader_exact_lookup D 192 N)
  have look' := look
  rw [code] at look'
  obtain ⟨bodyEq,hshapeEq,hdC,hbC,hnC⟩ := rlpWriteHeader_call_facts D 192 N _ _ _ look'
  have entryCode : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := by
    rw [callEntryStateHOLFinite]; exact code
  have hdE : (callEntryStateHOLFinite s callee).locals.lookup (ofString "dst")
      = some (.val (.word D)) := by rw [callEntryStateHOLFinite]; exact hdC
  have hbE : (callEntryStateHOLFinite s callee).locals.lookup (ofString "base")
      = some (.val (.word 192)) := by rw [callEntryStateHOLFinite]; exact hbC
  have hnE : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n")
      = some (.val (.word N)) := by rw [callEntryStateHOLFinite]; exact hnC
  have hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFunctionBody Guest.guestFn_rlp_write_header)).2.memory w = s.memory w := by
    rw [← bodyEq]
    exact (rlpWriteHeader_window (callEntryStateHOLFinite s callee) D N 192 w out
      hdE hnE hbE entryCode).trans (by rw [callEntryStateHOLFinite])
  exact tailCall_window s (ofString "rlp_write_header")
    [.var .local (ofString "dst"), .const (192#64), .var .local (ofString "payload_len")]
    [.val (.word D), .val (.word 192), .val (.word N)]
    (sourceFunctionBody Guest.guestFn_rlp_write_header) callee .one w argsEval look hbody

#print axioms rlpEncodeListHeader_window

end InitECandidate.Runtime
