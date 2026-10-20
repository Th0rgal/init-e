import InitECandidate.Runtime.RlpWriteHeaderTailWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The short-header prefix either returns (having stored the single length byte) or, in the
long-header branch, does nothing at all: a continuing outcome leaves the state unchanged. -/
theorem rlpWriteHeaderPrefix_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (N : BitVec 64) (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (mid : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s rlpWriteHeaderPrefix = (none, mid)) : mid = s := by
  rw [rlpWriteHeaderPrefix] at run
  by_cases hlt : (55#64) < N
  · have condEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.const (55#64)) (.var .local (ofString "n"))) = some (.val (.word 0#64)) := by
      simp [evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL,decide_eq_true hlt]
    rw [evaluateHOLFiniteState_ite,condEval] at run
    dsimp only at run
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl)] at run
    rw [evaluateHOLFiniteState_skip] at run
    exact ((Prod.mk.inj run).2).symm
  · have condEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.const (55#64)) (.var .local (ofString "n"))) = some (.val (.word 1#64)) := by
      simp [evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL,decide_eq_false hlt]
    rw [evaluateHOLFiniteState_ite,condEval] at run
    dsimp only at run
    rw [if_neg (by decide : ¬ ((1#64 : BitVec 64) = 0))] at run
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases storeRun : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with
    | mk sr sPost =>
      rw [storeRun] at run
      dsimp only at run
      cases sr with
      | none =>
        rw [evaluateHOLFiniteState_return] at run
        dsimp only at run
        simp only [evalHOLExact] at run
        split at run <;> simp at run
      | some res => simp at run

#print axioms rlpWriteHeaderPrefix_none

/-- **The actual `rlp_write_header`.**  It writes the list length header at `dst`: either the single
length byte (short header) or the length byte plus the real `rlp_be_len` byte count at `dst + 1`
written by `rlp_put_be`.  Every word outside the nine-byte window at `dst` keeps its cell. -/
theorem rlpWriteHeader_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (D N B0 w : BitVec 64) (out : ¬ MWin D 9 w)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hb : s.locals.lookup (ofString "base") = some (.val (.word B0)))
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_write_header)).2.memory w =
      s.memory w := by
  rw [source_rlpWriteHeader_body]
  rw [evaluateHOLFiniteState_seq_line780]
  cases prefixRun : evaluateHOLFiniteState s rlpWriteHeaderPrefix with
  | mk r mid =>
    cases r with
    | none =>
      have midEq := rlpWriteHeaderPrefix_none s N hn mid prefixRun
      rw [midEq]
      exact rlpWriteHeaderTail_window s D N B0 w out hd hn hb code
    | some res =>
      have hw := rlpWriteHeaderPrefix_window s D N B0 w out hd hn hb
      rw [prefixRun] at hw
      exact hw

#print axioms rlpWriteHeader_window

end InitECandidate.Runtime
