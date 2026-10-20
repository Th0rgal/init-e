import InitECandidate.Runtime.RlpWindowShift
import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.RlpBeLenCountBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The short-header prefix of the actual `rlp_write_header`: when `n >= 55` the list length fits in
one byte, which is stored at `dst` and `1` is returned. -/
def rlpWriteHeaderPrefix : ProgHOL 64 :=
  .ite (.cmp .notLower (.const (55#64)) (.var .local (ofString "n")))
    (.seq (.storeByte (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
      (.return (.const (1#64))))
    .skip

/-- The long-header tail of the actual `rlp_write_header`: the length byte at `dst`, then the big
endian byte count at `dst + 1`, then the total length. -/
def rlpWriteHeaderTail : ProgHOL 64 :=
  .decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
    (.seq (.storeByte (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .const (55#64), .var .local (ofString "ll")]))
      (.seq (.call (some (none,none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const (1#64)],
           .var .local (ofString "n"), .var .local (ofString "ll")])
        (.return (.op .add [.const (1#64), .var .local (ofString "ll")]))))

/-- The body equation of the actual `rlp_write_header`. -/
theorem source_rlpWriteHeader_body :
    sourceFunctionBody Guest.guestFn_rlp_write_header = .seq rlpWriteHeaderPrefix rlpWriteHeaderTail := by
  rw [rlpWriteHeaderPrefix,rlpWriteHeaderTail]
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_rlpWriteHeader_body

/-- The short-header branch writes at most the single byte at `dst`: either the list length fits in
one byte and only that byte is stored, or nothing is stored at all.  Every word outside the
nine-byte window at `dst` keeps its memory cell. -/
theorem rlpWriteHeaderPrefix_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D N B0 w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hb : s.locals.lookup (ofString "base") = some (.val (.word B0))) :
    (evaluateHOLFiniteState s rlpWriteHeaderPrefix).2.memory w = s.memory w := by
  have dstEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "dst")) = some (.val (.word D)) := by
    simp [evalHOLExact,lookupKvarHOLFinite,hd]
  have sep : w ≠ panByteAlignHOL D := by
    intro h
    refine out ⟨0,by decide,Or.inr ?_⟩
    rw [show (D + BitVec.ofNat 64 0) = D from by simp]
    exact h
  have store := evaluate_storeByte_memory_frame s (.var .local (ofString "dst"))
    (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]) D w dstEval sep
  rw [rlpWriteHeaderPrefix]
  by_cases hlt : (55#64) < N
  · have condEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.const (55#64)) (.var .local (ofString "n"))) = some (.val (.word 0#64)) := by
      simp [evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL,decide_eq_true hlt]
    rw [evaluateHOLFiniteState_ite,condEval]
    dsimp only
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl)]
    rw [evaluateHOLFiniteState_skip]
  · have condEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.const (55#64)) (.var .local (ofString "n"))) = some (.val (.word 1#64)) := by
      simp [evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL,decide_eq_false hlt]
    rw [evaluateHOLFiniteState_ite,condEval]
    dsimp only
    rw [if_neg (by decide : ¬ ((1#64 : BitVec 64) = 0))]
    rw [evaluateHOLFiniteState_seq_line780]
    dsimp only
    cases storeRun : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with
    | mk sr sPost =>
      rw [storeRun] at store
      dsimp only
      cases sr with
      | none =>
        exact (return_memory sPost (.const (1#64)) w).trans store
      | some res =>
        cases res <;> dsimp only <;> exact store

#print axioms rlpWriteHeaderPrefix_window

end InitECandidate.Runtime
