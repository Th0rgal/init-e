import InitECandidate.Runtime.RlpEncodeWordWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Shifting the base of a window by a word of at most nine bytes widens the window by nine. -/
theorem mwin_shift_word {D h w : BitVec 64} {N : Nat} (h9 : h.toNat ≤ 9)
    (win : MWin (D + h) N w) : MWin D (9 + N) w := by
  have inner : ∀ j : Nat, D + h + BitVec.ofNat 64 j = D + BitVec.ofNat 64 (h.toNat + j) := by
    intro j
    rw [BitVec.add_assoc]
    have step : h + BitVec.ofNat 64 j = BitVec.ofNat 64 (h.toNat + j) := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [step]
  obtain ⟨j, hj, hw | hw⟩ := win
  · exact ⟨h.toNat + j, by omega, Or.inl ((hw.trans (inner j)))⟩
  · exact ⟨h.toNat + j, by omega, Or.inr (by rw [hw]; exact congrArg panByteAlignHOL (inner j))⟩

#print axioms mwin_shift_word

/-- A single byte store never returns a value. -/
theorem storeByte_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (r : ValueHOL 64) (st : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s (.storeByte destination value) = (some (.returned r), st)) :
    False := by
  have control := evaluate_storeByte_control_frame s destination value
  rw [run] at control
  simp only [Prod.fst] at control
  exact control.1.elim (by simp) (by simp)

#print axioms storeByte_not_returned

/-- The store-and-return program only ever returns `1`. -/
theorem storeReturn_returns_one {F : Type} (s : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (r : ValueHOL 64)
    (run : (evaluateHOLFiniteState s
      (.seq (.storeByte destination value) (.return (.const (1#64))))).1 =
        some (.returned r)) : r = .val (.word (1#64)) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases storeRun : evaluateHOLFiniteState s (.storeByte destination value) with
  | mk sr sPost =>
    rw [storeRun] at run
    dsimp only at run
    cases sr with
    | none =>
      rw [evaluateHOLFiniteState_return] at run
      dsimp only at run
      simp only [evalHOLExact] at run
      split at run
      · injection run with h
        injection h with h
        exact h.symm
      · simp at run
    | some res =>
      have hres : res = .error := by
        have control := evaluate_storeByte_control_frame s destination value
        rw [storeRun] at control
        rcases control.1 with h | h
        · dsimp only at h
          simp at h
        · dsimp only at h
          exact Option.some.inj h
      subst hres
      simp at run

#print axioms storeReturn_returns_one

/-- A one-byte prefix only ever returns `1`. -/
theorem bytePrefix_returns_one {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (destination value : ExpHOL 64) (r : ValueHOL 64)
    (run : (evaluateHOLFiniteState s (.ite cond
      (.seq (.storeByte destination value) (.return (.const (1#64)))) .skip)).1 =
        some (.returned r)) : r = .val (.word (1#64)) := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · rename_i word heq
    by_cases hz : word = 0
    · rw [if_pos hz,evaluateHOLFiniteState_skip] at run
      simp at run
    · rw [if_neg hz] at run
      exact storeReturn_returns_one s destination value r run
  · simp at run

#print axioms bytePrefix_returns_one

end InitECandidate.Runtime
