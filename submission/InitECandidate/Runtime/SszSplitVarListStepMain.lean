import InitECandidate.Runtime.SszSplitVarListStepOutcome
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def SszSplitLocals (L : HolFiniteMapExact MlS (ValueHOL 64)) (p len first count arr i prev : BitVec 64) : Prop :=
  L.lookup (ofString "p") = some (.val (.word p)) ∧ L.lookup (ofString "len") = some (.val (.word len)) ∧
  L.lookup (ofString "first") = some (.val (.word first)) ∧ L.lookup (ofString "count") = some (.val (.word count)) ∧
  L.lookup (ofString "arr") = some (.val (.word arr)) ∧ L.lookup (ofString "i") = some (.val (.word i)) ∧
  L.lookup (ofString "prev") = some (.val (.word prev))

/-- One actual split iteration: either the offset o at index i is accepted
(o in [first,len], o ≥ prev) and both slice cells are written, or the
iteration exits abnormally. -/
theorem sszSplitStep_outcome {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p len first count arr i prev : BitVec 64)
    (look : SszSplitLocals s.locals p len first count arr i prev)
    (code : s.code = originalRuntimeCode) (positive : s.clock ≠ 0) :
    let out := evaluateHOLFiniteState s sszSplitStep
    s.clock ≤ out.2.clock + 1 ∧ out.2.clock ≤ s.clock ∧
      ((out.1 = none ∧ ∃ o, @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          sszSplitOffsetAt = some (.val (.word o)) ∧ ¬ o < first ∧ ¬ len < o ∧ ¬ o < prev ∧
          (Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true → s.memaddrs (arr + (i - 1) * 16 + 8)) ∧
          s.memaddrs (arr + i * 16) ∧
          ∃ L, out.2 = {s with locals := L, memory := sszSplitStepMemory s.memory arr p i o prev} ∧
            SszSplitLocals L p len first count arr (i + 1) o) ∨
       (∃ x, out.1 = some x ∧ SszAbnormal x)) := by
  obtain ⟨hp, hlen, hfirst, hcount, harr, hi, hprev⟩ := look
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18⟩ := sszsplit_names
  unfold sszSplitStep
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  cases init : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) sszSplitOffsetAt with
  | none =>
    simp only [init]
    exact ⟨Nat.le_succ _, Nat.le_refl _, Or.inr ⟨.error, rfl, by simp [SszAbnormal]⟩⟩
  | some v =>
    cases v
    case val wl =>
      cases wl with
      | word o =>
        simp only [init, shapeOfHOLExact, shapeEqHOL, if_true]
        let c := setVarHOLFinite (ofString "o") (.val (.word o)) s
        have up : ∀ k, k ≠ ofString "o" → c.locals.lookup k = s.locals.lookup k := by
          intro k hk; simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        have co : c.locals.lookup (ofString "o") = some (.val (.word o)) := by
          simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have cp := (up _ (Ne.symm n1)).trans hp
        have clen := (up _ (Ne.symm n2)).trans hlen
        have cfirst := (up _ (Ne.symm n3)).trans hfirst
        have carr := (up _ (Ne.symm n5)).trans harr
        have ci := (up _ (Ne.symm n6)).trans hi
        have cprev := (up _ (Ne.symm n7)).trans hprev
        have cCode : c.code = originalRuntimeCode := code
        have cClock : c.clock = s.clock := rfl
        change s.clock ≤ (evaluateHOLFiniteState c _).2.clock + 1 ∧ _
        by_cases bad : o < first ∨ len < o ∨ o < prev
        · rw [evaluateHOLFiniteState_seq_line780, sszSplitCheck_fail c o first len prev co cfirst clen cprev bad]
          obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal c 23 cCode (by rw [cClock]; exact positive)
          dsimp only
          rw [run]
          dsimp only
          rw [cClock] at c1 c2
          exact ⟨c1, c2, Or.inr ⟨x, run, abnormal⟩⟩
        · have ok : ¬ o < first ∧ ¬ len < o ∧ ¬ o < prev :=
            ⟨fun h => bad (Or.inl h), fun h => bad (Or.inr (Or.inl h)), fun h => bad (Or.inr (Or.inr h))⟩
          rw [evaluateHOLFiniteState_seq_line780, sszSplitCheck_pass c o first len prev co cfirst clen cprev ok]
          dsimp only
          rw [evaluateHOLFiniteState_seq_line780]
          unfold sszSplitStorePrev
          rw [evaluateHOLFiniteState_ite, sszSplit_guard_i c i ci]
          dsimp only
          by_cases pos : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess 0#64 i = true
          · simp only [pos, if_true]
            rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
            by_cases dom1 : s.memaddrs (arr + (i - 1) * 16 + 8)
            · rw [sszStore_in c _ _ _ _ (sszSplit_prevAddr c arr i carr ci) (sszSplit_diff c o prev "o" "prev" co cprev) dom1]
              dsimp only
              by_cases dom2 : s.memaddrs (arr + i * 16)
              · rw [sszSplitStep_rest_in c (wmem c.memory (arr + (i - 1) * 16 + 8) (o - prev)) p o arr i prev
                  cp co carr ci cprev dom2]
                dsimp only
                have hm : sszSplitStepMemory s.memory arr p i o prev =
                    wmem (wmem s.memory (arr + (i - 1) * 16 + 8) (o - prev)) (arr + i * 16) (p + o) := by
                  simp [sszSplitStepMemory, pos]
                refine ⟨Nat.le_succ _, Nat.le_refl _, Or.inl ⟨rfl, o, rfl, ok.1, ok.2.1, ok.2.2, fun _ => dom1, dom2,
                  _, by rw [hm]; rfl, ?_⟩⟩
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                  simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, resVarEq_lookup_ne,
                    n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16,
                    n17, n18, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7,
                    Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11, Ne.symm n12, Ne.symm n13, Ne.symm n14,
                    Ne.symm n15, Ne.symm n16, Ne.symm n17, Ne.symm n18, hp, hlen, hfirst, hcount, harr]
              · rw [sszSplitStep_rest_out c (wmem c.memory (arr + (i - 1) * 16 + 8) (o - prev)) p o arr i prev
                  cp co carr ci cprev dom2]
                exact ⟨Nat.le_succ _, Nat.le_refl _, Or.inr ⟨.error, rfl, by simp [SszAbnormal]⟩⟩
            · rw [sszStore_out c _ _ _ _ (sszSplit_prevAddr c arr i carr ci) (sszSplit_diff c o prev "o" "prev" co cprev) dom1]
              exact ⟨Nat.le_succ _, Nat.le_refl _, Or.inr ⟨.error, rfl, by simp [SszAbnormal]⟩⟩
          · simp only [pos, Bool.false_eq_true, if_false]
            rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
            dsimp only
            rw [show c = ({c with memory := c.memory} : PanSemStateFiniteExact 64 σ) from rfl]
            by_cases dom2 : s.memaddrs (arr + i * 16)
            · rw [sszSplitStep_rest_in c c.memory p o arr i prev cp co carr ci cprev dom2]
              dsimp only
              have hm : sszSplitStepMemory s.memory arr p i o prev = wmem s.memory (arr + i * 16) (p + o) := by
                simp [sszSplitStepMemory, pos]
              refine ⟨Nat.le_succ _, Nat.le_refl _, Or.inl ⟨rfl, o, rfl, ok.1, ok.2.1, ok.2.2, fun h => h.elim,
                dom2, _, by rw [hm]; rfl, ?_⟩⟩
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, resVarEq_lookup_ne,
                  n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16,
                  n17, n18, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7,
                  Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11, Ne.symm n12, Ne.symm n13, Ne.symm n14,
                  Ne.symm n15, Ne.symm n16, Ne.symm n17, Ne.symm n18, hp, hlen, hfirst, hcount, harr]
            · rw [sszSplitStep_rest_out c c.memory p o arr i prev cp co carr ci cprev dom2]
              exact ⟨Nat.le_succ _, Nat.le_refl _, Or.inr ⟨.error, rfl, by simp [SszAbnormal]⟩⟩
    all_goals
      simp only [init]
      simp [shapeOfHOLExact, shapeEqHOL, SszAbnormal]

#print axioms sszSplitStep_outcome
end InitECandidate.Runtime
