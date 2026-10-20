import InitECandidate.Runtime.RecWinBaseGD
/-!
`aqgd_whileExit` (a normal loop exit through a zero condition establishes an exit fact), `aqgd_callWin` (discarded
calls to window-spec callees), and the window spec of the actual `keccak256(p, n, out)` for any input length: it writes
only the state `[K, K + 200)`, the pad `[Pd, Pd + 136)` and the output `[O, O + 32)` (the absorb loop keeps
`i ≤ n`, so the final remainder is below 136 with no wrap).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section wx
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `aqgd_whileBreak_run` where a normal exit through a zero condition also establishes `X`. -/
theorem aqgd_whileExit_run {I C X Qb : GA → Mem → GA → Prop} (c : ExpHOL 64) (body : ProgHOL 64)
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 →
      C s.locals s.memory s.globals)
    (hx : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals →
      I s.locals s.memory s.globals → EV s c = some (.val (.word 0)) → X s.locals s.memory s.globals)
    (hb : AQGB D B A w Vn (fun L M G => I L M G ∧ C L M G) I Qb RR body) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (dom : DomD D B s)
    (aw : A s.globals) (sl : SL Vn s.locals) (pre : I s.locals s.memory s.globals) :
    (evaluateHOLFiniteState s (.while c body)).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s (.while c body)).1 →
      A (evaluateHOLFiniteState s (.while c body)).2.globals) ∧
    ((evaluateHOLFiniteState s (.while c body)).1 = none → SL Vn (evaluateHOLFiniteState s (.while c body)).2.locals ∧
      ∃ G', GIs (evaluateHOLFiniteState s (.while c body)).2.globals G' ∧
        ((I (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G' ∧
          X (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G') ∨
         Qb (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G')) ∧
    (∀ v, (evaluateHOLFiniteState s (.while c body)).1 = some (.returned v) →
      ∃ G', GIs (evaluateHOLFiniteState s (.while c body)).2.globals G' ∧
        RR v (evaluateHOLFiniteState s (.while c body)).2.memory G') ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · rename_i x hx'
    rw [evalHOLFinite_eq_toExact] at hx'
    split
    · rename_i nz
      split
      · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩
        all_goals simp_all [Continuing]
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have st := hb F (decClockHOLFinite s) code dom aw sl ⟨pre,hc s x aw dom pre sl hx' nz⟩
        have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk result middle =>
          rw [run] at st meta' remaining
          obtain ⟨m1,a1,n1,b1,r1,c1⟩ := st
          have smaller : middle.clock < s.clock := by
            change middle.clock ≤ s.clock - 1 at remaining
            omega
          cases result with
          | none =>
            obtain ⟨sl1,i1⟩ := n1 rfl
            obtain ⟨d1,d2,d3⟩ := dom
            have again := aqgd_whileExit_run c body hc hx hb middle (meta'.1.trans code)
              ⟨by rw [meta'.2.1]; exact d1,meta'.2.1.trans d2,meta'.2.2.1.trans d3⟩ (a1 (Or.inl rfl)) sl1 i1
            exact ⟨again.1.trans m1,again.2⟩
          | some result =>
            cases result with
            | «continue» => exact absurd rfl c1
            | «break» =>
              obtain ⟨sl1,q1⟩ := b1 rfl
              exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inl rfl))),fun _ => ⟨sl1,_,rfl,Or.inr q1⟩,
                (fun v e => by cases e),by simp,by simp⟩
            | returned v => exact ⟨m1,a1,(fun e => by cases e),fun v' e => by cases e; exact ⟨_,rfl,r1 v rfl⟩,
                by simp,by simp⟩
            | exception _ _ => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | finalFfi _ => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | error => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
            | timeOut => exact ⟨m1,a1,(fun e => by cases e),(fun v e => by cases e),by simp,by simp⟩
    · rename_i z
      have x0 : x = 0 := by simpa using z
      subst x0
      exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,_,rfl,Or.inl ⟨pre,hx s aw pre hx'⟩⟩,(fun v e => by cases e),by simp,by simp⟩
  · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩
    all_goals simp_all [Continuing]
termination_by s.clock

theorem aqgd_whileExit {I C X Qb : GA → Mem → GA → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 →
      C s.locals s.memory s.globals)
    (hx : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals →
      I s.locals s.memory s.globals → EV s c = some (.val (.word 0)) → X s.locals s.memory s.globals)
    (hb : AQGB D B A w Vn (fun L M G => I L M G ∧ C L M G) I Qb RR body) :
    AQGD D B A w Vn I (fun L M G => (I L M G ∧ X L M G) ∨ Qb L M G) RR (.while c body) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  exact aqgd_whileExit_run c body hc hx hb s code dom aw sl pre

#print axioms aqgd_whileExit
end wx
section cw
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A discarded call to a callee with a memory-and-globals-indexed spec; the caller's locals predicate is kept. -/
theorem aqgd_callWin {LP : GA → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (Pe' : GA → GA → Prop)
    (hspec : ∀ L0, LP L0 → ∀ (M0 : Mem) (G0 : GA), AQGD D B A w (fun _ => False)
      (fun L M G => Pe' L0 L ∧ M = M0 ∧ G = G0) (fun _ _ _ => True) (fun _ _ _ => True) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals → LP s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) → Pe' s.locals callee) :
    AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LP L) RR (.call (some (none,none)) function arguments) :=
  aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (M0 : Mem) (G0 : GA) (L : GA) (M : Mem) (G : GA) => Pe' L0 L ∧ M = M0 ∧ G = G0)
    (RRe := fun _ _ _ _ _ _ => True) _ _ _ _ _ installed allOne
    (fun L0 M0 G0 pre => aqgd_conseq (hspec L0 pre M0 G0) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ _ => trivial))
    (fun s values callee rs aw H hH pre _ args lookup => by
      unfold GIs at hH; subst hH
      exact ⟨hpe s values callee rs aw pre args lookup,rfl,rfl⟩)
    (fun _ _ _ _ _ _ pre _ => pre)

#print axioms aqgd_callWin
end cw

/-- Locals of `keccak256(p, n, out)`. -/
def KL0 (Pp N O : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "p") = some (.val (.word Pp)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
    L.lookup (ofString "out") = some (.val (.word O))

theorem kl0_upd {Pp N O : BitVec 64} (n : MlS) (h1 : ofString "p" ≠ n) (h2 : ofString "n" ≠ n)
    (h3 : ofString "out" ≠ n) (L : GA) (v : ValueHOL 64) (h : KL0 Pp N O L) : KL0 Pp N O (L.update (n,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,by rw [lookup_update_ne' _ _ h2]; exact h.2.1,
    by rw [lookup_update_ne' _ _ h3]; exact h.2.2⟩

theorem kl0_res {Pp N O : BitVec 64} (n : MlS) (h1 : ofString "p" ≠ n) (h2 : ofString "n" ≠ n)
    (h3 : ofString "out" ≠ n) (L : GA) (o : Option (ValueHOL 64)) (h : KL0 Pp N O L) : KL0 Pp N O (L.resVarEq (n,o)) :=
  ⟨by rw [resVarEq_lookup_ne' _ _ _ _ h1]; exact h.1,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact h.2.1,
    by rw [resVarEq_lookup_ne' _ _ _ _ h3]; exact h.2.2⟩

section kw
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

/-- The actual `keccak256(p, n, out)` for any input length writes only the state `[K, K + 200)`, the pad
`[Pd, Pd + 136)` and the output `[O, O + 32)`. -/
theorem keccak_wn (K Pd : BitVec 64)
    (hA : ∀ g, A g → g.lookup (ofString "keccak_st") = some (.val (.word K)) ∧
      g.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (Pp N O : BitVec 64) (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => KL0 Pp N O L) (fun _ _ _ => True) (fun _ _ _ => True)
      (sourceFunctionBody Guest.guestFn_keccak256) := by
  rw [source_keccak_hol]; unfold keccakHOL
  let K1 := fun L : GA => KL0 Pp N O L ∧ L.lookup (ofString "stp") = some (.val (.word K))
  have k1u : ∀ (n : MlS), ofString "p" ≠ n → ofString "n" ≠ n → ofString "out" ≠ n → ofString "stp" ≠ n →
      ∀ L v, K1 L → K1 (L.update (n,v)) := fun n h1 h2 h3 h4 L v ⟨h,hs⟩ =>
    ⟨kl0_upd n h1 h2 h3 L v h,by rw [lookup_update_ne' _ _ h4]; exact hs⟩
  -- stp = keccak_st
  refine aqgd_dec (Pb := fun L _ _ => K1 L) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H aw hG pre _ ev _
    unfold GIs at hG; subst hG
    have hk := (hA _ aw).1
    simp [EV,evalHOLExact,hk] at ev; subst ev
    exact ⟨kl0_upd _ (by decide) (by decide) (by decide) _ _ pre,lookup_update_eq' _ _ _⟩
  -- memzero(stp, 200)
  refine aqgd_seq (aqgd_callWin (LP := K1) _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp)
    (fun _ L => L.lookup (ofString "dst") = some (.val (.word K)) ∧ L.lookup (ofString "n") = some (.val (.word 200#64)))
    (fun _ _ M0 G0 => aqgd_conseq (memzero_wn K 200#64 (by decide) oK M0 G0) (fun _ _ _ ⟨h,m,g⟩ => ⟨h,m,g⟩)
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial))
    (fun s values callee rs _ ⟨_,hs⟩ args lookup => by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hs] at args
      subst args
      have e := callee_eq originalRuntimeCode_memzero_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- i = 0; absorb loop
  let KI := fun L : GA => K1 L ∧ ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat
  refine aqgd_dec (Pb := fun L _ _ => KI L) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H aw hG pre _ ev _
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨k1u _ (by decide) (by decide) (by decide) (by decide) _ _ pre,0#64,lookup_update_eq' _ _ _,by simp⟩
  refine aqgd_seq (aqgd_whileExit (I := fun L _ _ => KI L)
    (C := fun L _ _ => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ (I + 136#64).toNat ≤ N.toNat)
    (X := fun L _ _ => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ N.toNat < (I + 136#64).toNat)
    (Qb := fun _ _ _ => False) _ ?_ ?_ ?_) ?_
  · intro F s x aw _ ⟨⟨⟨_,hn,_⟩,_⟩,I,hi,_⟩ _ ev nz
    simp [EV,evalHOLExact,evalListHOLExact,hi,hn,wordOpHOL,wordOp,valueIsWord,valueWord,
      Compiler.Encoders.Asm.wordCmpHOL] at ev
    by_cases h : I + 136#64 ≤ N
    · exact ⟨I,hi,BitVec.le_def.mp h⟩
    · rw [if_neg h] at ev; exact absurd ev.symm nz
  · intro F s aw ⟨⟨⟨_,hn,_⟩,_⟩,I,hi,_⟩ ev
    simp [EV,evalHOLExact,evalListHOLExact,hi,hn,wordOpHOL,wordOp,valueIsWord,valueWord,
      Compiler.Encoders.Asm.wordCmpHOL] at ev
    exact ⟨I,hi,BitVec.lt_def.mp ev⟩
  · refine aqgb_of_aqgd (aqgd_seq (aqgd_callWin
      (LP := fun L => KI L ∧ ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧
        (I + 136#64).toNat ≤ N.toNat) _ _ _ _ _ originalRuntimeCode_keccakAbsorb_lookup (by simp)
      (fun _ L => L.lookup (ofString "stp") = some (.val (.word K)) ∧
        ∃ Bk : BitVec 64, L.lookup (ofString "blk") = some (.val (.word Bk)))
      (fun _ _ M0 G0 => aqgd_conseq (absorb_wn K oK M0 G0) (fun _ _ _ h => h) (fun _ _ _ h => h)
        (fun _ _ _ _ => trivial))
      (fun s values callee rs _ ⟨⟨⟨⟨hp,_,_⟩,hs⟩,_⟩,I,hi,_⟩ args lookup => by
        rw [evalListHOLFinite_eq_toExact] at args
        simp [evalListHOLExact,evalHOLExact,hs,hp,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at args
        subst args
        have e := callee_eq originalRuntimeCode_keccakAbsorb_lookup lookup
        exact ⟨by rw [e]; simp (config := {decide := true}),Pp + I,by rw [e]; simp (config := {decide := true})⟩))
      (aqgd_assignLocal _ _ ?_))
    intro F s v _ _ ⟨⟨k1,_⟩,I,hi,hle⟩ _ ev
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    exact ⟨k1u _ (by decide) (by decide) (by decide) (by decide) _ _ k1,_,lookup_update_eq' _ _ _,hle⟩
  -- rem = n - i (< 136)
  let KR := fun L : GA => K1 L ∧ ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧
    ∃ R : BitVec 64, L.lookup (ofString "rem") = some (.val (.word R)) ∧ R.toNat < 136
  refine aqgd_dec (Pb := fun L _ _ => KR L) (Qb := fun _ _ _ => False) _ _ _ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v H aw hG pre _ ev _
    rcases pre with ⟨⟨k1,I,hi,hle⟩,I',hi',hlt⟩ | h
    · rw [hi] at hi'; simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hi'; subst hi'
      simp [EV,evalHOLExact,evalListHOLExact,hi,k1.1.2.1,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      have e1 : (N - I).toNat = N.toNat - I.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
      have e2 : (I + 136#64).toNat = (I.toNat + 136) % 2 ^ 64 := by simp [BitVec.toNat_add]
      exact ⟨k1u _ (by decide) (by decide) (by decide) (by decide) _ _ k1,I,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hi,_,lookup_update_eq' _ _ _,by omega⟩
    · exact h.elim
  -- memzero(keccak_pad, 136)
  refine aqgd_seq (aqgd_callWin (LP := KR) _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp)
    (fun _ L => L.lookup (ofString "dst") = some (.val (.word Pd)) ∧
      L.lookup (ofString "n") = some (.val (.word 136#64)))
    (fun _ _ M0 G0 => aqgd_conseq (memzero_wn Pd 136#64 (by decide) oP M0 G0) (fun _ _ _ h => h)
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial))
    (fun s values callee rs aw _ args lookup => by
      have hp := (hA _ aw).2
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hp] at args
      subst args
      have e := callee_eq originalRuntimeCode_memzero_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- memcpy(keccak_pad, p + i, rem)
  refine aqgd_seq (aqgd_callWin (LP := KR) _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp)
    (fun L0 L => L.lookup (ofString "dst") = some (.val (.word Pd)) ∧
      L.lookup (ofString "src") = some (.val (.word (wordOf L0 (ofString "p") + wordOf L0 (ofString "i")))) ∧
      L.lookup (ofString "n") = some (.val (.word (wordOf L0 (ofString "rem")))))
    (fun L0 ⟨_,_,_,R,hr,hR⟩ M0 G0 => by
      rw [wordOf_eq hr]
      exact aqgd_conseq (memcpy_wn Pd _ R (by omega) (mwin_mono (by omega) oP) M0 G0) (fun _ _ _ h => h)
        (fun _ _ _ h => h) (fun _ _ _ _ => trivial))
    (fun s values callee rs aw ⟨⟨⟨hp,_,_⟩,_⟩,I,hi,R,hr,_⟩ args lookup => by
      have hpd := (hA _ aw).2
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hpd,hp,hi,hr,wordOpHOL,wordOp,valueIsWord,valueWord] at args
      subst args
      have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
      rw [wordOf_eq hp,wordOf_eq hi,wordOf_eq hr]
      exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
        by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- st8 keccak_pad + rem, 1
  refine aqgd_seq (aqgd_storeByte (Q := fun L _ _ => KR L) _ _ ?_) ?_
  · intro F s aw _ ⟨k1,I,hi,R,hr,hR⟩ _
    have hpd := (hA _ aw).2
    refine ⟨Pd + R,by simp [EV,evalHOLExact,evalListHOLExact,hpd,hr,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => oP ⟨R.toNat,hR,Or.inr (by simpa using e)⟩,fun _ _ => ⟨k1,I,hi,R,hr,hR⟩⟩
  -- st8 keccak_pad + 135, ld8(...) | 128
  refine aqgd_seq (aqgd_storeByte (Q := fun L _ _ => KR L) _ _ ?_) ?_
  · intro F s aw _ pre _
    have hpd := (hA _ aw).2
    refine ⟨Pd + 135#64,by simp [EV,evalHOLExact,evalListHOLExact,hpd,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => oP ⟨135,by decide,Or.inr e⟩,fun _ _ => pre⟩
  -- keccak_absorb_block(stp, keccak_pad)
  refine aqgd_seq (aqgd_callWin (LP := KR) _ _ _ _ _ originalRuntimeCode_keccakAbsorb_lookup (by simp)
    (fun _ L => L.lookup (ofString "stp") = some (.val (.word K)) ∧
      ∃ Bk : BitVec 64, L.lookup (ofString "blk") = some (.val (.word Bk)))
    (fun _ _ M0 G0 => aqgd_conseq (absorb_wn K oK M0 G0) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ _ _ _ => trivial))
    (fun s values callee rs aw ⟨⟨_,hs⟩,_⟩ args lookup => by
      have hpd := (hA _ aw).2
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hs,hpd] at args
      subst args
      have e := callee_eq originalRuntimeCode_keccakAbsorb_lookup lookup
      exact ⟨by rw [e]; simp (config := {decide := true}),Pd,by rw [e]; simp (config := {decide := true})⟩)) ?_
  -- output
  refine aqgd_seq (Q := fun L _ _ => KR L) (aqgd_iteT _ ?_ ?_) (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial))
  · have st : ∀ (k : Nat) (e d : ExpHOL 64), k < 32 → (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
        KR s.locals → EV s d = some (.val (.word (O + BitVec.ofNat 64 k)))) →
        AQGD D B A w (fun _ => False) (fun L _ _ => KR L) (fun L _ _ => KR L) (fun _ _ _ => True)
          (.store d (.load .one e)) := fun k e d hk hd =>
      aqgd_store _ _ (fun s _ _ hG pre _ => ⟨_,hd s (by unfold GIs at hG; subst hG; exact pre),
        fun h => oO ⟨k,hk,Or.inl h⟩,fun _ _ => by unfold GIs at hG; subst hG; exact pre⟩)
        (fun s x _ _ _ _ _ ev => ev_load_one_word s _ x ev)
    have ho : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), KR s.locals →
        s.locals.lookup (ofString "out") = some (.val (.word O)) := fun s pre => pre.1.1.2.2
    refine aqgd_seq (st 0 _ _ (by decide) (fun s pre => by simp [EV,evalHOLExact,ho s pre])) ?_
    refine aqgd_seq (st 8 _ _ (by decide) (fun s pre => by
      simp [EV,evalHOLExact,evalListHOLExact,ho s pre,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
    refine aqgd_seq (st 16 _ _ (by decide) (fun s pre => by
      simp [EV,evalHOLExact,evalListHOLExact,ho s pre,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
    exact st 24 _ _ (by decide) (fun s pre => by
      simp [EV,evalHOLExact,evalListHOLExact,ho s pre,wordOpHOL,wordOp,valueIsWord,valueWord])
  · exact aqgd_callWin (LP := KR) _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp)
      (fun _ L => L.lookup (ofString "dst") = some (.val (.word O)) ∧
        L.lookup (ofString "src") = some (.val (.word K)) ∧ L.lookup (ofString "n") = some (.val (.word 32#64)))
      (fun _ _ M0 G0 => aqgd_conseq (memcpy_wn O K 32#64 (by decide) oO M0 G0) (fun _ _ _ h => h)
        (fun _ _ _ h => h) (fun _ _ _ _ => trivial))
      (fun s values callee rs aw ⟨⟨⟨_,_,ho⟩,hs⟩,_⟩ args lookup => by
        rw [evalListHOLFinite_eq_toExact] at args
        simp [evalListHOLExact,evalHOLExact,hs,ho] at args
        subst args
        have e := callee_eq originalRuntimeCode_memcpy_lookup lookup
        exact ⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true}),
          by rw [e]; simp (config := {decide := true})⟩)

#print axioms keccak_wn
end kw
end InitECandidate.Runtime
