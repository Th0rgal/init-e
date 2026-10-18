import InitECandidate.Runtime.SszCheckOffsetsChecks
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem resVarEq_lookup_ne {β : Type} (m : HolFiniteMapExact MlS β) (key k : MlS) (opt : Option β)
    (ne : k ≠ key) : (HolFiniteMapExact.resVarEq m (key, opt)).lookup k = m.lookup k := by
  cases opt with
  | none => simp [FDOMSUB_HOL, ne]
  | some v => simp [FUPDATE_HOL, ne]

def memWord (m : BitVec 64 → HolWordLab 64) (address : BitVec 64) : BitVec 64 :=
  match m address with | .word w => w

/-- One accepted offset: in the domain, within [fixed,len], and not below its predecessor. -/
def SszOffsetOK {σ : Type} (s : PanSemStateFiniteExact 64 σ) (offs fixed len i : BitVec 64) : Prop :=
  s.memaddrs (offs + i * 8#64) ∧ ¬ memWord s.memory (offs + i * 8#64) < fixed ∧
    ¬ len < memWord s.memory (offs + i * 8#64) ∧
    (Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true →
      s.memaddrs (offs + i * 8#64 - 8#64) ∧
      ¬ memWord s.memory (offs + i * 8#64) < memWord s.memory (offs + i * 8#64 - 8#64))

theorem sszcheck_names : ofString "o" ≠ ofString "offs" ∧ ofString "o" ≠ ofString "n" ∧
    ofString "o" ≠ ofString "fixed" ∧ ofString "o" ≠ ofString "len" ∧ ofString "o" ≠ ofString "i" ∧
    ofString "i" ≠ ofString "offs" ∧ ofString "i" ≠ ofString "n" ∧ ofString "i" ≠ ofString "fixed" ∧
    ofString "i" ≠ ofString "len" := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide_cbv

/-- Failure branches of one iteration: terminal, non-control, non-return. -/
def SszAbnormal (x : PanSemResultExact 64) : Prop :=
  x ≠ .continue ∧ x ≠ .timeOut ∧ x ≠ .break ∧ ∀ v, x ≠ .returned v

theorem sszFail_abnormal {σ : Type} (c : PanSemStateFiniteExact 64 σ) (code : BitVec 64)
    (installed : c.code = originalRuntimeCode) (positive : c.clock ≠ 0) :
    ∃ x, (evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const code])).1 = some x ∧
      SszAbnormal x ∧
      c.clock ≤ (evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const code])).2.clock + 1 ∧
      (evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const code])).2.clock ≤ c.clock := by
  have args : evalListHOLFinite c (h := fun address => Classical.propDecidable (c.memaddrs address))
      [.const code] = some [.val (.word code)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have fail := sszFail_literal_call c code installed
  have control := evaluate_sszFail_call_not_control c (.const code) code installed args
  cases run : evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const code]) with
  | mk result post =>
    rw [run] at fail control
    dsimp only at fail control ⊢
    cases result with
    | none => exact absurd rfl fail.2.2.2.1
    | some x =>
      refine ⟨x, rfl, ⟨fun h => control.2 (by rw [h]), fun h => fail.2.2.1 positive (by rw [h]),
        fun h => control.1 (by rw [h]), fun v h => fail.2.2.2.2 v (by rw [h])⟩, fail.1, fail.2.1⟩

#print axioms sszFail_abnormal

theorem sszcheck_assign {σ : Type} (c : PanSemStateFiniteExact 64 σ) (i : BitVec 64)
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i))) :
    evaluateHOLFiniteState c (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (i + 1))) c) := by
  simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, lookupKvarHOLExact,
    isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem sszCheckStep_outcome {σ : Type} (s : PanSemStateFiniteExact 64 σ) (offs n fixed len i : BitVec 64)
    (hoffs : s.locals.lookup (ofString "offs") = some (.val (.word offs)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hfixed : s.locals.lookup (ofString "fixed") = some (.val (.word fixed)))
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (code : s.code = originalRuntimeCode) (positive : s.clock ≠ 0) :
    let out := evaluateHOLFiniteState s sszCheckStep
    s.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ s.clock ∧
      ((out.1 = none ∧ (∃ L, out.2 = {s with locals := L} ∧ L.lookup (ofString "offs") = some (.val (.word offs)) ∧
          L.lookup (ofString "n") = some (.val (.word n)) ∧ L.lookup (ofString "fixed") = some (.val (.word fixed)) ∧
          L.lookup (ofString "len") = some (.val (.word len)) ∧ L.lookup (ofString "i") = some (.val (.word (i + 1)))) ∧
        SszOffsetOK s offs fixed len i) ∨
       (∃ x, out.1 = some x ∧ SszAbnormal x)) := by
  obtain ⟨n1,n2,n3,n4,n5,n6,n7,n8,n9⟩ := sszcheck_names
  unfold sszCheckStep
  rw [evaluateHOLFiniteState_dec_total]
  by_cases dom : s.memaddrs (offs + i * 8#64)
  · cases mem : s.memory (offs + i * 8#64) with
    | word w =>
      have init : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.load .one sszOffsetAddress) = some (.val (.word w)) := by
        simp [sszOffsetAddress, evalHOLExact, evalListHOLExact, hoffs, hi, wordOpHOL, wordOp, valueIsWord,
          valueWord, panOpHOL, memLoadHOLExact, isWfShapeExactHOL, dom, mem]
      simp only [init, shapeOfHOLExact, shapeEqHOL, if_true]
      let c := setVarHOLFinite (ofString "o") (.val (.word w)) s
      have co : c.locals.lookup (ofString "o") = some (.val (.word w)) := by
        simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have up : ∀ k, k ≠ ofString "o" → c.locals.lookup k = s.locals.lookup k := by
        intro k hk; simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, hk]
      have cfixed := (up _ (Ne.symm n3)).trans hfixed
      have clen := (up _ (Ne.symm n4)).trans hlen
      have coffs := (up _ (Ne.symm n1)).trans hoffs
      have ci := (up _ (Ne.symm n5)).trans hi
      have cCode : c.code = originalRuntimeCode := code
      have cClock : c.clock = s.clock := rfl
      have restoreClock : ∀ (p : PanSemStateFiniteExact 64 σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
          ({p with locals := L} : PanSemStateFiniteExact 64 σ).clock = p.clock := fun _ _ => rfl
      change s.clock ≤ (evaluateHOLFiniteState c _).2.clock + 1 ∧ _
      by_cases bad : w < fixed ∨ len < w
      · rw [evaluateHOLFiniteState_seq_line780, sszCheckRange_fail c w fixed len co cfixed clen bad]
        obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal c 10 cCode (by rw [cClock]; exact positive)
        try dsimp only
        rw [run]
        try dsimp only
        rw [cClock] at c1 c2
        exact ⟨c1, c2, Or.inr ⟨x, run, abnormal⟩⟩
      · have ok : ¬ w < fixed ∧ ¬ len < w := ⟨fun h => bad (Or.inl h), fun h => bad (Or.inr h)⟩
        rw [evaluateHOLFiniteState_seq_line780, sszCheckRange_pass c w fixed len co cfixed clen ok]
        try dsimp only
        rw [evaluateHOLFiniteState_seq_line780, sszCheckPrevious_eval c w offs i co coffs ci]
        have memEq : c.memory = s.memory := rfl
        have domEq : c.memaddrs = s.memaddrs := rfl
        have wEq : memWord s.memory (offs + i * 8#64) = w := by simp [memWord, mem]
        have finish : ∀ (pos : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true →
              s.memaddrs (offs + i * 8#64 - 8#64) ∧ ¬ w < memWord s.memory (offs + i * 8#64 - 8#64)),
            let out := evaluateHOLFiniteState c (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
            s.clock ≤ ({out.2 with locals := out.2.locals.resVarEq (ofString "o", s.locals.lookup (ofString "o"))} :
                PanSemStateFiniteExact 64 σ).clock + 1 ∧
              ({out.2 with locals := out.2.locals.resVarEq (ofString "o", s.locals.lookup (ofString "o"))} :
                PanSemStateFiniteExact 64 σ).clock ≤ s.clock ∧
              ((out.1 = none ∧ (∃ L, ({out.2 with locals := out.2.locals.resVarEq (ofString "o", s.locals.lookup (ofString "o"))} :
                PanSemStateFiniteExact 64 σ) = {s with locals := L} ∧ L.lookup (ofString "offs") = some (.val (.word offs)) ∧
                L.lookup (ofString "n") = some (.val (.word n)) ∧ L.lookup (ofString "fixed") = some (.val (.word fixed)) ∧
                L.lookup (ofString "len") = some (.val (.word len)) ∧ L.lookup (ofString "i") = some (.val (.word (i + 1)))) ∧
                SszOffsetOK s offs fixed len i) ∨ (∃ x, out.1 = some x ∧ SszAbnormal x)) := by
          intro pos
          rw [sszcheck_assign c i ci]
          refine ⟨by simp [setVarHOLFinite, c], by simp [setVarHOLFinite, c], Or.inl ⟨rfl, ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
          · simp [setVarHOLFinite, c, HolFiniteMapExact.lookup_update, FUPDATE, resVarEq_lookup_ne _ _ _ _ (Ne.symm n1), n1, n6, Ne.symm n1, Ne.symm n6, hoffs]
          · simp [setVarHOLFinite, c, HolFiniteMapExact.lookup_update, FUPDATE, resVarEq_lookup_ne _ _ _ _ (Ne.symm n2), n2, n7, Ne.symm n2, Ne.symm n7, hn]
          · simp [setVarHOLFinite, c, HolFiniteMapExact.lookup_update, FUPDATE, resVarEq_lookup_ne _ _ _ _ (Ne.symm n3), n3, n8, Ne.symm n3, Ne.symm n8, hfixed]
          · simp [setVarHOLFinite, c, HolFiniteMapExact.lookup_update, FUPDATE, resVarEq_lookup_ne _ _ _ _ (Ne.symm n4), n4, n9, Ne.symm n4, Ne.symm n9, hlen]
          · simp [setVarHOLFinite, c, HolFiniteMapExact.lookup_update, FUPDATE, resVarEq_lookup_ne _ _ _ _ (Ne.symm n5), n5, Ne.symm n5]
          · refine ⟨dom, by rw [wEq]; exact ok.1, by rw [wEq]; exact ok.2, ?_⟩
            intro p; rw [wEq]; exact pos p
        by_cases positiveI : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true
        · simp only [positiveI, if_true]
          by_cases dom2 : s.memaddrs (offs + i * 8#64 - 8#64)
          · rw [domEq, if_pos dom2]
            by_cases less : w < memWord s.memory (offs + i * 8#64 - 8#64)
            · rw [if_pos]
              rotate_left
              · exact less
              · obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal c 11 cCode (by rw [cClock]; exact positive)
                try dsimp only
                rw [run]
                try dsimp only
                rw [cClock] at c1 c2
                exact ⟨c1, c2, Or.inr ⟨x, run, abnormal⟩⟩
            · rw [if_neg]
              rotate_left
              · exact less
              · dsimp only
                exact finish (fun _ => ⟨dom2, less⟩)
          · rw [domEq, if_neg dom2]
            exact ⟨by simp; omega, by simp [cClock], Or.inr ⟨.error, rfl, by simp [SszAbnormal]⟩⟩
        · simp only [positiveI, Bool.false_eq_true, if_false]
          try dsimp only
          exact finish (fun h => absurd h positiveI)
  · have init : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one sszOffsetAddress) = none := by
      simp [sszOffsetAddress, evalHOLExact, evalListHOLExact, hoffs, hi, wordOpHOL, wordOp, valueIsWord,
        valueWord, panOpHOL, memLoadHOLExact, isWfShapeExactHOL, dom]
    simp only [init]
    exact ⟨by omega, Nat.le_refl _, Or.inr ⟨.error, rfl, by simp [SszAbnormal]⟩⟩

#print axioms sszCheckStep_outcome
end InitECandidate.Runtime
