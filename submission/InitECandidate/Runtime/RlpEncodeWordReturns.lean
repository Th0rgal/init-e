import InitECandidate.Runtime.RlpEncodeWordWindow
import InitECandidate.Runtime.RlpWriteHeaderReturns
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- **The actual `rlp_encode_word` returns a word of at most nine bytes**: one byte for a zero or
small word, and `1 + ll` with the byte count `ll` of the word at most eight otherwise. -/
theorem rlpEncodeWord_returns_le_nine {F : Type} (s : PanSemStateFiniteExact 64 F)
    (V : BitVec 64) (code : s.code = originalRuntimeCode) (r : ValueHOL 64)
    (hw : s.locals.lookup (ofString "w") = some (.val (.word V)))
    (run : (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_encode_word)).1 =
      some (.returned r)) : ∃ H : BitVec 64, r = .val (.word H) ∧ H.toNat ≤ 9 := by
  rw [source_rlpEncodeWord_body] at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases zeroRun : evaluateHOLFiniteState s rlpEncodeWordZero with
  | mk r0 mid0 =>
    rw [zeroRun] at run
    dsimp only at run
    cases r0 with
    | some res =>
      cases res with
      | returned v =>
        have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
        rw [← hvr]
        refine ⟨1#64, bytePrefix_returns_one s
          (.cmp .equal (.var .local (ofString "w")) (.const (0#64)))
          (.var .local (ofString "dst")) (.const (128#64)) v ?_, by decide⟩
        show (evaluateHOLFiniteState s rlpEncodeWordZero).1 = some (.returned v)
        rw [zeroRun]
      | _ => simp at run
    | none =>
      have zEq := rlpEncodeWordZero_none s mid0 zeroRun
      rw [zEq] at run
      dsimp only at run
      rw [evaluateHOLFiniteState_seq_line780] at run
      cases smallRun : evaluateHOLFiniteState s rlpEncodeWordSmall with
      | mk r1 mid1 =>
        rw [smallRun] at run
        dsimp only at run
        cases r1 with
        | some res =>
          cases res with
          | returned v =>
            have hvr : v = r := PanSemResultExact.returned.inj (Option.some.inj run)
            rw [← hvr]
            refine ⟨1#64, bytePrefix_returns_one s
              (.cmp .lower (.var .local (ofString "w")) (.const (128#64)))
              (.var .local (ofString "dst")) (.var .local (ofString "w")) v ?_, by decide⟩
            show (evaluateHOLFiniteState s rlpEncodeWordSmall).1 = some (.returned v)
            rw [smallRun]
          | _ => simp at run
        | none =>
          have sEq := rlpEncodeWordSmall_none s mid1 smallRun
          rw [sEq] at run
          dsimp only at run
          rw [rlpEncodeWordLong] at run
          exact rlpLongTailDecCall_returns s V
            (.op .add [.const (128#64), .var .local (ofString "ll")])
            (ofString "w") hw code r run

#print axioms rlpEncodeWord_returns_le_nine

end InitECandidate.Runtime
