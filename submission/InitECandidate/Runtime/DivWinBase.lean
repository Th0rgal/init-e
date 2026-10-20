import InitECandidate.Runtime.CheckTransactionGD
/-!
Building blocks for the `u256_ws` window frame of the actual `u256_divmod` chain: an exit-condition loop rule, the
actual `digits_len` (count bound, nonzero when a digit is nonzero) and `u256_to_digits` (exactly the eight digit words).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section loopE
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

theorem aqgd_whileE_run {I C E Qb : GA → Mem → GA → Prop} (c : ExpHOL 64) (body : ProgHOL 64)
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 →
      C s.locals s.memory s.globals)
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x = 0 →
      E s.locals s.memory s.globals)
    (hb : AQGB D B A w Vn (fun L M G => I L M G ∧ C L M G) I Qb RR body) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (dom : DomD D B s)
    (aw : A s.globals) (sl : SL Vn s.locals) (pre : I s.locals s.memory s.globals) :
    (evaluateHOLFiniteState s (.while c body)).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s (.while c body)).1 →
      A (evaluateHOLFiniteState s (.while c body)).2.globals) ∧
    ((evaluateHOLFiniteState s (.while c body)).1 = none → SL Vn (evaluateHOLFiniteState s (.while c body)).2.locals ∧
      ∃ G', GIs (evaluateHOLFiniteState s (.while c body)).2.globals G' ∧
        ((I (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G' ∧
          E (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G') ∨
         Qb (evaluateHOLFiniteState s (.while c body)).2.locals (evaluateHOLFiniteState s (.while c body)).2.memory G')) ∧
    (∀ v, (evaluateHOLFiniteState s (.while c body)).1 = some (.returned v) →
      ∃ G', GIs (evaluateHOLFiniteState s (.while c body)).2.globals G' ∧
        RR v (evaluateHOLFiniteState s (.while c body)).2.memory G') ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.while c body)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · rename_i x hx
    rw [evalHOLFinite_eq_toExact] at hx
    split
    · rename_i nz
      split
      · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩
        all_goals simp_all [Continuing]
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have st := hb F (decClockHOLFinite s) code dom aw sl ⟨pre,hc s x aw dom pre sl hx nz⟩
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
            have again := aqgd_whileE_run c body hc he hb middle (meta'.1.trans code)
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
      exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,_,rfl,Or.inl ⟨pre,he s x aw dom pre sl hx (by simpa using z)⟩⟩,
        (fun v e => by cases e),by simp,by simp⟩
  · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩
    all_goals simp_all [Continuing]
termination_by s.clock

/-- A loop rule whose normal exit also records the exit condition. -/
theorem aqgd_whileE {I C E Qb : GA → Mem → GA → Prop} (c : ExpHOL 64) {body : ProgHOL 64}
    (hc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x ≠ 0 →
      C s.locals s.memory s.globals)
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64), A s.globals → DomD D B s →
      I s.locals s.memory s.globals → SL Vn s.locals → EV s c = some (.val (.word x)) → x = 0 →
      E s.locals s.memory s.globals)
    (hb : AQGB D B A w Vn (fun L M G => I L M G ∧ C L M G) I Qb RR body) :
    AQGD D B A w Vn I (fun L M G => (I L M G ∧ E L M G) ∨ Qb L M G) RR (.while c body) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  exact aqgd_whileE_run c body hc he hb s code dom aw sl pre

#print axioms aqgd_whileE
end loopE

def dlBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.const 0#64) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 1#64], ExpHOL.const 8#64]])) (ExpHOL.const 0#64)) (ProgHOL.return (ExpHOL.var VarKind.local (ofString "n"))) ProgHOL.skip) (ProgHOL.assign VarKind.local (ofString "n") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 1#64])))) (ProgHOL.return (ExpHOL.const 0#64))

theorem dlBody_eq : sourceFunctionBody Guest.guestFn_digits_len = dlBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_digits_len,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Return of `digits_len(p, n0)`: a word at most `n0`, nonzero when some digit below `n0` is nonzero. -/
def DLRetW (P N0 : BitVec 64) (M0 : Mem) (v : ValueHOL 64) : Prop :=
  ∃ n : BitVec 64, v = .val (.word n) ∧ n.toNat ≤ N0.toNat ∧
    ((∃ k : BitVec 64, k.toNat < N0.toNat ∧ M0 (P + k * 8) ≠ .word 0) → 1 ≤ n.toNat)

/-- Loop invariant of `digits_len`: digits from the current count up to `n0` are zero. -/
def DLInv (P N0 : BitVec 64) (M0 : Mem) (G0 : GA) (L : GA) (M : Mem) (G : GA) : Prop :=
  L.lookup (ofString "p") = some (.val (.word P)) ∧ M = M0 ∧ G = G0 ∧
    ∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)) ∧ N.toNat ≤ N0.toNat ∧
      ∀ k : BitVec 64, N.toNat ≤ k.toNat → k.toNat < N0.toNat → M0 (P + k * 8) = .word 0

section dl
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

theorem digitsLen_spec (P N0 : BitVec 64) (M0 : Mem) (G0 : GA) :
    AQGD D B A w (fun _ => False)
      (fun L M G => L.lookup (ofString "p") = some (.val (.word P)) ∧
        L.lookup (ofString "n") = some (.val (.word N0)) ∧ M = M0 ∧ G = G0)
      (fun _ _ _ => False) (fun v M' G' => M' = M0 ∧ G' = G0 ∧ DLRetW P N0 M0 v) dlBody := by
  unfold dlBody
  refine aqgd_seq (Q := fun L M G => DLInv P N0 M0 G0 L M G ∧ L.lookup (ofString "n") = some (.val (.word 0)))
    (aqgd_conseq (aqgd_whileE (I := DLInv P N0 M0 G0)
      (C := fun L _ _ => ∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)) ∧ 0 < N.toNat)
      (E := fun L _ _ => L.lookup (ofString "n") = some (.val (.word 0))) (Qb := fun _ _ _ => False) _
      ?_ ?_ (aqgb_of_aqgd ?_)) ?_ (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)) ?_
  · intro F s x _ _ ⟨_,_,_,N,hn,_⟩ _ hx nz
    simp [EV,evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL] at hx
    refine ⟨N,hn,?_⟩
    by_cases h : (0#64 : BitVec 64) < N
    · simpa [BitVec.lt_def] using h
    · simp [h] at hx; exact absurd hx.symm nz
  · intro F s x _ _ ⟨_,_,_,N,hn,_⟩ _ hx z
    simp [EV,evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL] at hx
    have e : N = 0#64 := by
      by_cases h : (0#64 : BitVec 64) < N
      · simp [h] at hx; subst z; exact absurd hx (by decide)
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.lt_def] at h; simpa using h
    rw [e] at hn; exact hn
  · refine aqgd_seq (Q := fun L M G => (DLInv P N0 M0 G0 L M G ∧
        ∃ N : BitVec 64, L.lookup (ofString "n") = some (.val (.word N)) ∧ 0 < N.toNat) ∧
        M (P + (((match L.lookup (ofString "n") with | some (.val (.word N)) => N | _ => 0) - 1) * 8)) = .word 0)
      (aqgd_ite (CT := fun _ _ _ => True)
        (CF := fun L M _ => M (P + (((match L.lookup (ofString "n") with | some (.val (.word N)) => N | _ => 0) - 1) * 8)) = .word 0) _ ?_
        (aqgd_return _ ?_) (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)))
      (aqgd_assignLocal _ _ ?_)
    · intro F s x _ _ _ ⟨⟨hp,_,_,N,hn,_⟩,_⟩ _ hx
      simp [EV,evalHOLExact,evalListHOLExact,hn,hp,Compiler.Encoders.Asm.wordCmpHOL,memLoadHOLExact,wordOpHOL,
        wordOp,valueIsWord,valueWord,panOpHOL] at hx
      refine ⟨fun _ => trivial,fun z => ?_⟩
      rw [hn]; dsimp only
      have key : s.memory (P + (N - 1#64) * 8#64) = .word 0 := by
        by_cases hd : s.memaddrs (P + (N - 1#64) * 8#64)
        · cases hm : s.memory (P + (N - 1#64) * 8#64) with
          | word y =>
            rw [if_pos hd,hm] at hx
            simp at hx
            by_cases hy : y = 0#64
            · rw [hy]; rfl
            · simp [hy] at hx; subst z; exact absurd hx (by decide)
        · rw [if_neg hd] at hx; simp at hx
      exact key
    · intro F s v _ _ _ ⟨⟨⟨hp,hM,hG,N,hn,hle,_⟩,N',hn',pos⟩,_⟩ _ ev
      rw [hn] at hn'; simp at hn'; subst hn'
      simp [EV,evalHOLExact,hn] at ev; subst ev
      exact ⟨hM,hG,N,rfl,hle,fun _ => pos⟩
    · intro F s v _ _ ⟨⟨⟨hp,hM,hG,N,hn,hle,hz⟩,N',hn',pos⟩,hm⟩ _ ev
      rw [hn] at hn'; simp at hn'; subst hn'
      simp [EV,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      simp only [hn] at hm
      have e1 : (N - 1).toNat = N.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
      refine ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE]; exact hp,hM,hG,N - 1,
        by simp [HolFiniteMapExact.lookup_update,FUPDATE],by rw [e1]; omega,fun k h1 h2 => ?_⟩
      by_cases hk : k = N - 1
      · subst hk; rw [← hM]; exact hm
      · have : k.toNat ≠ (N - 1).toNat := fun e => hk (BitVec.eq_of_toNat_eq e)
        exact hz k (by omega) h2
  · intro L M G ⟨hp,hn,hM,hG⟩
    exact ⟨hp,hM,hG,N0,hn,le_refl _,fun k h1 h2 => absurd h2 (by omega)⟩
  · refine aqgd_return _ (fun s v _ _ _ ⟨⟨_,hM,hG,N,hn,_,hz⟩,hn0⟩ _ ev => ?_)
    simp [EV,evalHOLExact] at ev; subst ev
    rw [hn] at hn0; simp at hn0; subst hn0
    refine ⟨hM,hG,0,rfl,by simp,fun ⟨k,hk,hne⟩ => absurd (hz k (by simp) hk) hne⟩

end dl

def u2dBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.store (ExpHOL.var VarKind.local (ofString "p")) (ExpHOL.op BinOp.and [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.const 4294967295#64])) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 8#64]) (ExpHOL.shift Shift.lsr (ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "a"))) (ExpHOL.const 32#64))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 16#64]) (ExpHOL.op BinOp.and [ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.const 4294967295#64])) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 24#64]) (ExpHOL.shift Shift.lsr (ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "a"))) (ExpHOL.const 32#64))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 32#64]) (ExpHOL.op BinOp.and [ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.const 4294967295#64])) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 40#64]) (ExpHOL.shift Shift.lsr (ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "a"))) (ExpHOL.const 32#64))) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 48#64]) (ExpHOL.op BinOp.and [ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.const 4294967295#64])) (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.const 56#64]) (ExpHOL.shift Shift.lsr (ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "a"))) (ExpHOL.const 32#64))) (ProgHOL.return (ExpHOL.const 0#64)))))))))

theorem u2dBody_eq : sourceFunctionBody Guest.guestFn_u256_to_digits = u2dBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_u256_to_digits,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- The `k`-th 32-bit digit of a four-word value. -/
def dig (a0 a1 a2 a3 : BitVec 64) : Nat → BitVec 64
  | 0 => a0 &&& 4294967295 | 1 => a0 >>> 32 | 2 => a1 &&& 4294967295 | 3 => a1 >>> 32
  | 4 => a2 &&& 4294967295 | 5 => a2 >>> 32 | 6 => a3 &&& 4294967295 | _ => a3 >>> 32

/-- After the first `i` digit stores of `u256_to_digits` at `P`. -/
def U2D (P a0 a1 a2 a3 : BitVec 64) (M0 : Mem) (i : Nat) (M : Mem) : Prop :=
  (∀ x, (∀ k, k < 8 → x ≠ P + BitVec.ofNat 64 (8 * k)) → M x = M0 x) ∧
    ∀ k, k < i → M (P + BitVec.ofNat 64 (8 * k)) = .word (dig a0 a1 a2 a3 k)

theorem off_inj {P : BitVec 64} {j k : Nat} (hj : j < 8) (hk : k < 8)
    (e : P + BitVec.ofNat 64 (8 * k) = P + BitVec.ofNat 64 (8 * j)) : k = j := by
  have := congrArg BitVec.toNat e
  have hP := P.isLt
  simp [BitVec.toNat_add,BitVec.toNat_ofNat] at this
  omega

theorem u2d_step {P a0 a1 a2 a3 : BitVec 64} {M0 M : Mem} {i : Nat} (hi : i < 8) (h : U2D P a0 a1 a2 a3 M0 i M) :
    U2D P a0 a1 a2 a3 M0 (i + 1)
      (fun x => if x = P + BitVec.ofNat 64 (8 * i) then .word (dig a0 a1 a2 a3 i) else M x) := by
  obtain ⟨fr,vals⟩ := h
  refine ⟨fun x hx => by dsimp only; rw [if_neg (hx i hi)]; exact fr x hx,fun k hk => ?_⟩
  dsimp only
  by_cases e : k = i
  · subst e; simp
  · rw [if_neg (fun h' => e (off_inj hi (by omega) h'))]; exact vals k (by omega)

#print axioms u2d_step

/-- Locals of `u256_to_digits(p, a)`. -/
def LPA (P a0 a1 a2 a3 : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "p") = some (.val (.word P)) ∧
    L.lookup (ofString "a") = some (.rStruct [.val (.word a0),.val (.word a1),.val (.word a2),.val (.word a3)])

section u2d
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}
  {RR : ValueHOL 64 → Mem → GA → Prop} {P a0 a1 a2 a3 : BitVec 64} {M0 : Mem}

theorem aqgd_u2d_store (i : Nat) (hi : i < 8) (d v : ExpHOL 64) (LP : GA → Prop)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LP s.locals →
      EV s d = some (.val (.word (P + BitVec.ofNat 64 (8 * i)))))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
      x = .val (.word (dig a0 a1 a2 a3 i)))
    (hw : w ≠ P + BitVec.ofNat 64 (8 * i)) :
    AQGD D B A w (fun _ => False) (fun L M _ => LP L ∧ U2D P a0 a1 a2 a3 M0 i M)
      (fun L M _ => LP L ∧ U2D P a0 a1 a2 a3 M0 (i + 1) M) RR (.store d v) :=
  aqgd_store _ _ (fun s _ _ _ ⟨lp,h⟩ _ => ⟨_,hd s lp,hw,fun y hy => ⟨lp,by
      have e := hv s _ lp hy
      simp only [ValueHOL.val.injEq,HolWordLab.word.injEq] at e
      subst e; exact u2d_step hi h⟩⟩)
    (fun s x _ _ _ ⟨lp,_⟩ _ ev => ⟨_,hv s x lp ev⟩)

/-- The actual `u256_to_digits(p, a)` writes the eight 32-bit digits of `a` at `p, p+8, …, p+56` and nothing else. -/
theorem u2d_spec (hw : ∀ k, k < 8 → w ≠ P + BitVec.ofNat 64 (8 * k)) :
    AQGD D B A w (fun _ => False) (fun L M _ => LPA P a0 a1 a2 a3 L ∧ M = M0) (fun _ _ _ => False)
      (fun _ M' _ => U2D P a0 a1 a2 a3 M0 8 M') u2dBody := by
  unfold u2dBody
  refine aqgd_conseq (P := fun L M _ => LPA P a0 a1 a2 a3 L ∧ U2D P a0 a1 a2 a3 M0 0 M) ?_
    (fun _ _ _ ⟨lp,hM⟩ => ⟨lp,hM ▸ ⟨fun _ _ => rfl,fun _ h => absurd h (by omega)⟩⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 0 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 0 (by decide))) ?_
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 1 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 1 (by decide))) ?_
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 2 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 2 (by decide))) ?_
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 3 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 3 (by decide))) ?_
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 4 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 4 (by decide))) ?_
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 5 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 5 (by decide))) ?_
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 6 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 6 (by decide))) ?_
  refine aqgd_seq (aqgd_u2d_store (P := P) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (M0 := M0) 7 (by decide) _ _
    (LPA P a0 a1 a2 a3) (fun s ⟨hp,ha⟩ => by simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨hp,ha⟩ ev => by simp [EV,evalHOLExact,evalListHOLExact,ha,wordOpHOL,wordOp,valueIsWord,valueWord,dig,wordShiftHOL] at ev ⊢; exact ev.symm)
    (hw 7 (by decide))) ?_
  exact aqgd_return _ (fun _ _ _ _ _ ⟨_,h⟩ _ _ => h)

#print axioms u2d_spec
end u2d
/-- A word whose low and high 32-bit halves are zero is zero. -/
theorem half_zero (a : BitVec 64) (h1 : a &&& 4294967295 = 0) (h2 : a >>> 32 = 0) : a = 0 := by
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  simp [BitVec.toNat_and,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at e1 e2
  apply BitVec.eq_of_toNat_eq
  have : (4294967295 : Nat) = 2^32 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod] at e1
  simp
  omega
#print axioms half_zero
#print axioms digitsLen_spec
end InitECandidate.Runtime
