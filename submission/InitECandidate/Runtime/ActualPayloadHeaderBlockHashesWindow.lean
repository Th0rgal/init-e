import InitECandidate.Runtime.PayloadHeaderTailSources
import InitECandidate.Runtime.KeccakFullCallWindow
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- **The block-hashes statement (50) of `payload_header` keeps a watched cell.**

The real statement is `keccak256(load [pl + 64], load [pl + 72], bh)`, whose result is handed straight
to `return h`.  This is a suffix frame from the actual source: the hash call writes only the
permutation state window, the padding window and the 32-byte `bh` output window, and the following
`return h` writes nothing, so any watched cell outside those three windows keeps its value through the
whole statement -- whether the hash returns or fails. -/
theorem actual_payload_header_block_hashes_window {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pl st pad hdr source size output watched : BitVec 64)
    (plLocal : state.locals.lookup (ofString "pl") = some (.val (.word pl)))
    (sourceDomain : state.memaddrs (pl + (64#64)))
    (sourceCell : state.memory (pl + (64#64)) = .word source)
    (sizeDomain : state.memaddrs (pl + (72#64)))
    (sizeCell : state.memory (pl + (72#64)) = .word size)
    (hdrLocal : state.locals.lookup (ofString "h") = some (.val (.word hdr)))
    (outputLocal : state.locals.lookup (ofString "bh") = some (.val (.word output)))
    (stGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word st)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (code : state.code = originalRuntimeCode)
    (small : size.toNat ≤ 134217712)
    (budget : size.toNat * 20 + 43 ≤ state.clock)
    (outsideState : ¬ MWin st 200 watched) (outsidePad : ¬ MWin pad 136 watched)
    (outsideOutput : ¬ MWin output 32 watched) :
    (evaluateHOLFiniteState state (actualPayloadHeaderAt 50)).2.memory watched =
      state.memory watched := by
  let arguments : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .local (ofString "pl"), .const (64#64)]),
     .load .one (.op .add [.var .local (ofString "pl"), .const (72#64)]),
     .var .local (ofString "bh")]
  have sourceEval := actual_payload_header_eval_load_word state (ofString "pl") pl (64#64) source
    plLocal sourceDomain sourceCell
  have sizeEval := actual_payload_header_eval_load_word state (ofString "pl") pl (72#64) size
    plLocal sizeDomain sizeCell
  have outputEval := actual_payload_header_eval_local_value state (ofString "bh") (.val (.word output))
    outputLocal
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      arguments = some [.val (.word source),.val (.word size),.val (.word output)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [arguments,evalListHOLExact]
    rw [sourceEval,sizeEval,outputEval]
  have frame := keccak_full_call_window state st pad source size output watched arguments stGlobal padGlobal
    args small code budget outsideState outsidePad outsideOutput
  rw [source_actual_payload_header_block_hashes,evaluateHOLFiniteState_seq_line780]
  cases callRun : evaluateHOLFiniteState state
    (.call (some (none,none)) (ofString "keccak256") arguments) with
  | mk result next =>
    rw [callRun] at frame
    cases result with
    | some failed => exact frame.1
    | none =>
      show (evaluateHOLFiniteState next (actualPayloadHeaderAt 51)).2.memory watched =
        state.memory watched
      have locals := evaluate_discard_call_success_locals state (ofString "keccak256") arguments
        (by rw [callRun])
      rw [callRun] at locals
      have nextHdr : next.locals.lookup (ofString "h") = some (.val (.word hdr)) := by
        rw [locals]; exact hdrLocal
      rw [actual_payload_header_return_h next hdr nextHdr]
      exact frame.1

#print axioms actual_payload_header_block_hashes_window

end InitECandidate.Runtime
