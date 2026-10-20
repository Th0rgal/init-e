import InitECandidate.Runtime.RlpPutBeStepLocals
import InitECandidate.Runtime.RlpHeaderLenMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The counting step of the actual `rlp_be_len`: `v >>= 8; n += 1`. -/
def rlpBeLenStep : ProgHOL 64 :=
  .seq (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const (8#64))))
    (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const (1#64)]))

/-- The counting loop of the actual `rlp_be_len`: `while v != 0 { v >>= 8; n += 1 }`. -/
def rlpBeLenLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "v")) (.const (0#64))) rlpBeLenStep

/-- The whole actual `rlp_be_len` body. -/
def rlpBeLenBody : ProgHOL 64 :=
  .dec (ofString "n") .one (.const (0#64)) (.seq rlpBeLenLoop (.return (.var .local (ofString "n"))))

/-- The body of `rlp_be_len` is the counting program. -/
theorem rlpBeLenBody_source : rlpBeLenBody = sourceFunctionBody Guest.guestFn_rlp_be_len := by
  rw [rlpBeLenBody,rlpBeLenLoop,rlpBeLenStep,source_rlpBeLen_body]

#print axioms rlpBeLenBody_source

theorem rlpBeLen_shiftToNat_nat (I : BitVec 64) : (I >>> (8 : Nat)).toNat = I.toNat / 256 := by
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem rlpBeLen_shiftToNat (I : BitVec 64) : (I >>> 8#64).toNat = I.toNat / 256 := by
  show (I >>> (8#64 : BitVec 64).toNat).toNat = I.toNat / 256
  rw [show (8#64 : BitVec 64).toNat = 8 from by decide]
  exact rlpBeLen_shiftToNat_nat I

#print axioms rlpBeLen_shiftToNat

theorem rlpBeLen_div_pow256_succ (a n : Nat) : a / 256 ^ (n + 1) = a / 256 ^ n / 256 := by
  rw [Nat.pow_succ,Nat.div_div_eq_div_mul]

#print axioms rlpBeLen_div_pow256_succ

theorem rlpBeLen_pow256_eight : 256 ^ 8 = 2 ^ 64 := by norm_num

#print axioms rlpBeLen_pow256_eight

/-- The clock of a fixed step is clamped but the locals survive. -/
theorem fixClock_locals {F : Type} (old : PanSemStateFiniteExact 64 F)
    (step : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) :
    (fixClockHOLFinite old step).2.locals = step.2.locals := rfl

#print axioms fixClock_locals

/-- The shift assign of one counting step, exactly. -/
theorem rlpBeLenShiftAssign {F : Type} (s : PanSemStateFiniteExact 64 F) (I : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word I))) :
    evaluateHOLFiniteState s (.assign .local (ofString "v")
        (.shift .lsr (.var .local (ofString "v")) (.const (8#64)))) =
      (none, setVarHOLFinite (ofString "v") (.val (.word (I >>> 8#64))) s) := by
  rw [evaluateHOLFiniteState_assign]
  simp [evalHOLExact,hv,wordShiftHOL,valueIsWord,valueWord,
    isValidValueHOLExact,lookupKvarHOLExact,shapeEqHOL,shapeOfHOLExact,setKvarHOLFinite]

#print axioms rlpBeLenShiftAssign

/-- The counter increment of one counting step, exactly. -/
theorem rlpBeLenIncrementAssign {F : Type} (s : PanSemStateFiniteExact 64 F) (Nv : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word Nv))) :
    evaluateHOLFiniteState s (.assign .local (ofString "n")
        (.op .add [.var .local (ofString "n"), .const (1#64)])) =
      (none, setVarHOLFinite (ofString "n") (.val (.word (Nv + 1#64))) s) := by
  rw [evaluateHOLFiniteState_assign]
  simp [evalListHOLExact,evalHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord,
    isValidValueHOLExact,lookupKvarHOLExact,shapeEqHOL,shapeOfHOLExact,setKvarHOLFinite]

#print axioms rlpBeLenIncrementAssign

/-- The exact post state of one counting step. -/
def rlpBeLenNext {F : Type} (s : PanSemStateFiniteExact 64 F) (I Nv : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "n") (.val (.word (Nv + 1#64)))
    (setVarHOLFinite (ofString "v") (.val (.word (I >>> 8#64))) s)

/-- One counting step, exactly: the shift then the increment both succeed. -/
theorem rlpBeLenStep_exact {F : Type} (s : PanSemStateFiniteExact 64 F) (I Nv : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word I)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word Nv))) :
    evaluateHOLFiniteState s rlpBeLenStep = (none, rlpBeLenNext s I Nv) := by
  have shift := rlpBeLenShiftAssign s I hv
  have hnShift : (setVarHOLFinite (ofString "v") (.val (.word (I >>> 8#64))) s).locals.lookup
      (ofString "n") = some (.val (.word Nv)) :=
    lookup_setVar_ne s (ofString "v") (ofString "n") _ _ (by decide) hn
  have inc := rlpBeLenIncrementAssign _ Nv hnShift
  rw [rlpBeLenStep,seq_normal (s := s) (first := _) (second := _) shift,inc,rlpBeLenNext]

#print axioms rlpBeLenStep_exact

/-- The loop condition is zero exactly when the counted word is zero. -/
theorem rlpBeLenCond_zero {F : Type} (s : PanSemStateFiniteExact 64 F) (I : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word I))) (hI : I = 0#64) :
    @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const (0#64))) =
      some (.val (.word 0#64)) := by
  simp [evalHOLExact,hv,hI,Compiler.Encoders.Asm.wordCmpHOL]

#print axioms rlpBeLenCond_zero

/-- The loop condition is one exactly when the counted word is nonzero. -/
theorem rlpBeLenCond_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (I : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word I))) (hI : I ≠ 0#64) :
    @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const (0#64))) =
      some (.val (.word 1#64)) := by
  simp [evalHOLExact,hv,hI,Compiler.Encoders.Asm.wordCmpHOL]

#print axioms rlpBeLenCond_pos

/-- **The byte count of `rlp_be_len` is at most eight.** Whatever the outcome of its counting loop,
the local `n` that the trailing `return` reports counts the right shifts of one 64-bit word, so it
never exceeds eight. -/
theorem rlpBeLenLoop_count_aux {F : Type} (V : BitVec 64) (m : Nat) :
    ∀ (s : PanSemStateFiniteExact 64 F) (I Nv : BitVec 64),
      s.locals.lookup (ofString "v") = some (.val (.word I)) →
      s.locals.lookup (ofString "n") = some (.val (.word Nv)) →
      I.toNat = V.toNat / 256 ^ Nv.toNat →
      Nv.toNat ≤ 8 → 8 - Nv.toNat ≤ m →
      ∀ (r : Option (PanSemResultExact 64)) (s'), evaluateHOLFiniteState s rlpBeLenLoop = (r, s') →
        (¬ ∃ v, r = some (.returned v)) ∧
        (∀ v, s'.locals.lookup (ofString "n") = some v →
          ∃ N', v = .val (.word N') ∧ N'.toNat ≤ 8) := by
  induction m with
  | zero =>
    intro s I Nv hv hn hinv hNv hle r s' run
    have hNv8 : Nv.toNat = 8 := by omega
    have hzero : I.toNat = 0 := by
      rw [hinv,hNv8,rlpBeLen_pow256_eight,Nat.div_eq_of_lt V.isLt]
    have hI : I = 0#64 := by
      apply BitVec.toNat_inj.mp
      simpa using hzero
    have hcond := rlpBeLenCond_zero s I hv hI
    rw [rlpBeLenLoop,evaluateHOLFiniteState_while_total,hcond] at run
    dsimp only at run
    rw [if_neg (by decide : ¬ ((0#64) ≠ 0))] at run
    obtain ⟨hr,hs⟩ := Prod.mk.inj run
    subst hr
    subst hs
    refine ⟨?_,?_⟩
    · intro ⟨v,hv'⟩
      cases hv'
    · intro v hv'
      rw [hn] at hv'
      injection hv' with h
      exact ⟨Nv,h.symm,hNv⟩
  | succ m ih =>
    intro s I Nv hv hn hinv hNv hle r s' run
    by_cases hI : I = 0#64
    · have hcond := rlpBeLenCond_zero s I hv hI
      rw [rlpBeLenLoop,evaluateHOLFiniteState_while_total,hcond] at run
      dsimp only at run
      rw [if_neg (by decide : ¬ ((0#64) ≠ 0))] at run
      obtain ⟨hr,hs⟩ := Prod.mk.inj run
      subst hr
      subst hs
      refine ⟨?_,?_⟩
      · intro ⟨v,hv'⟩
        cases hv'
      · intro v hv'
        rw [hn] at hv'
        injection hv' with h
        exact ⟨Nv,h.symm,hNv⟩
    · have hI0 : I.toNat ≠ 0 := by
        intro h
        apply hI
        apply BitVec.toNat_inj.mp
        simpa using h
      have hpow : 256 ^ Nv.toNat ≤ V.toNat := by
        have hnot : ¬ V.toNat < 256 ^ Nv.toNat := by
          intro hlt
          exact hI0 (by rw [hinv,Nat.div_eq_of_lt hlt])
        exact Nat.le_of_not_lt hnot
      have hNvlt : Nv.toNat < 8 := by
        by_contra h
        have h8 : 8 ≤ Nv.toNat := by omega
        have hle8 : 256 ^ 8 ≤ 256 ^ Nv.toNat := Nat.pow_le_pow_right (by norm_num) h8
        rw [rlpBeLen_pow256_eight] at hle8
        omega
      have hNv1 : (Nv + 1#64).toNat = Nv.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt]
        · simp
        · simp
          omega
      have hle8 : (Nv + 1#64).toNat ≤ 8 := by rw [hNv1]; omega
      have hcond := rlpBeLenCond_pos s I hv hI
      rw [rlpBeLenLoop,evaluateHOLFiniteState_while_total,hcond] at run
      dsimp only at run
      rw [if_pos (by decide : ((1#64) ≠ 0))] at run
      by_cases hclock : s.clock = 0
      · rw [if_pos hclock] at run
        obtain ⟨hr,hs⟩ := Prod.mk.inj run
        subst hr
        subst hs
        refine ⟨?_,?_⟩
        · intro ⟨v,hv'⟩
          cases hv'
        · intro v hv'
          simp [emptyLocalsHOLFinite] at hv'
      · rw [if_neg hclock] at run
        have stepRun := rlpBeLenStep_exact (decClockHOLFinite s) I Nv hv hn
        rw [stepRun] at run
        dsimp only at run
        have hvA : (fixClockHOLFinite (decClockHOLFinite s)
            ((none : Option (PanSemResultExact 64)), rlpBeLenNext (decClockHOLFinite s) I Nv)).2.locals.lookup (ofString "v") =
            some (.val (.word (I >>> 8#64))) := by
          rw [fixClock_locals]
          exact lookup_setVar_ne _ (ofString "n") (ofString "v") _ _
            (by decide) (lookup_setVar_eq _ (ofString "v") _)
        have hnA : (fixClockHOLFinite (decClockHOLFinite s)
            ((none : Option (PanSemResultExact 64)), rlpBeLenNext (decClockHOLFinite s) I Nv)).2.locals.lookup (ofString "n") =
            some (.val (.word (Nv + 1#64))) := by
          rw [fixClock_locals]
          exact lookup_setVar_eq _ (ofString "n") _
        have hinvA : (I >>> 8#64).toNat = V.toNat / 256 ^ (Nv + 1#64).toNat := by
          rw [rlpBeLen_shiftToNat,hNv1,hinv,rlpBeLen_div_pow256_succ]
        have hleA : 8 - (Nv + 1#64).toNat ≤ m := by rw [hNv1]; omega
        exact ih _ (I >>> 8#64) (Nv + 1#64) hvA hnA hinvA hle8 hleA r s' run

#print axioms rlpBeLenLoop_count_aux

/-- **`rlp_be_len` counts at most eight bytes.** It returns a word `n ≤ 8` whenever it returns
normally, so every writer whose prefix length comes from it writes at most eight bytes past its
destination. -/
theorem rlpBeLen_returns_le_eight {F : Type} (s : PanSemStateFiniteExact 64 F) (V : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word V))) :
    ∀ (r : ValueHOL 64),
      (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_be_len)).1 =
          some (.returned r) →
        ∃ N : BitVec 64, r = .val (.word N) ∧ N.toNat ≤ 8 := by
  intro r run
  rw [← rlpBeLenBody_source] at run
  rw [rlpBeLenBody,evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  have initEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (0#64)) = some (.val (.word 0#64)) := by
    simp [evalHOLExact]
  rw [initEval] at run
  dsimp only at run
  have shapeTrue : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeTrue] at run
  dsimp only at run
  have hv0 : (setVarHOLFinite (ofString "n") (.val (.word 0#64)) s).locals.lookup
      (ofString "v") = some (.val (.word V)) :=
    lookup_setVar_ne s (ofString "n") (ofString "v") _ _ (by decide) hv
  have hn0 : (setVarHOLFinite (ofString "n") (.val (.word 0#64)) s).locals.lookup
      (ofString "n") = some (.val (.word 0#64)) :=
    lookup_setVar_eq s (ofString "n") _
  rw [evaluateHOLFiniteState_seq_line780] at run
  dsimp only at run
  cases loopRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word 0#64)) s)
      rlpBeLenLoop with
  | mk lr loopPost =>
    rw [loopRun] at run
    dsimp only at run
    obtain ⟨hnotReturned,hlen⟩ := rlpBeLenLoop_count_aux V (8 - (0#64).toNat) _
      V (0#64) hv0 hn0 (by simp) (by decide) (le_refl _) lr loopPost loopRun
    cases lr with
    | none =>
      cases hlook : loopPost.locals.lookup (ofString "n") with
      | none =>
        rw [evaluateHOLFiniteState_return] at run
        dsimp only at run
        simp [evalHOLExact,lookupKvarHOLFinite,hlook] at run
      | some v =>
        obtain ⟨N', hvEq, hNle⟩ := hlen v hlook
        have varEval : @evalHOLExact 64 F _ loopPost.toExact
            (fun a => Classical.propDecidable (loopPost.memaddrs a))
            (.var .local (ofString "n")) = some (.val (.word N')) := by
          rw [← hvEq]
          simp [evalHOLExact,lookupKvarHOLFinite,hlook]
        rw [evaluateHOLFiniteState_return,varEval] at run
        dsimp only at run
        have hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL loopPost.structs
            (shapeOfHOLExact (.val (.word N'))) ≤ 32 := by
          simp [Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL,shapeOfHOLExact]
        rw [if_pos hsize] at run
        dsimp only at run
        injection run with h1
        injection h1 with h2
        exact ⟨N',h2.symm,hNle⟩
    | some res =>
      dsimp only at run
      injection run with hval
      exact absurd ⟨r,by rw [hval]⟩ hnotReturned

#print axioms rlpBeLen_returns_le_eight

end InitECandidate.Runtime
