import InitECandidate.Runtime.ProcessTxUGD
import InitECandidate.Runtime.DivmnuWindowGD
import InitECandidate.Runtime.OriginalEncodeCode
/-!
Domain-fence infrastructure for the `encode_transaction` writers: a successful store learns its (aligned) address is
in the memory domain `D`; with an explicit fence `Fence D DF` (every domain address below `DF`) this bounds write
cursors. Fenced store rules keep every word below an aligned lower fence `Lo`. Specs of the actual `rlp_be_len`
(result at most 8) and `rlp_put_be` (writes only `[dst, dst+n)`, and on return `dst + n ≤ DF + 8`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A byte store that completes normally stored into a domain word. -/
theorem storeByte_none_dom' {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (a : BitVec 64)
    (ha : EV s d = some (.val (.word a)))
    (h : (evaluateHOLFiniteState s (.storeByte d v)).1 = none) : s.memaddrs (panByteAlignHOL a) := by
  rw [evaluateHOLFiniteState_storeByte] at h
  simp only [EV] at ha
  rw [ha] at h
  dsimp only at h
  split at h
  · split at h
    · rename_i mem hm
      unfold panMemStoreByteWord8HOL at hm
      dsimp only at hm
      by_cases hd : s.memaddrs (panByteAlignHOL a)
      · exact hd
      · rw [if_neg hd] at hm; cases hm
    · cases h
  · cases h

#print axioms storeByte_none_dom'
theorem align_toNat (a : BitVec 64) : (panByteAlignHOL a).toNat = a.toNat / 8 * 8 := by
  have : Nat.log2 (64 / 8) = 3 := by decide
  simp only [panByteAlignHOL,this]
  rw [BitVec.toNat_ofNat]
  have := a.isLt
  omega

section st
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A byte store at or above an aligned lower fence `Lo` keeps every word below `Lo`; a normal outcome learns the
stored word is in the domain. -/
theorem r_stb {LP LQ : GA → Prop} (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ Lo.toNat ≤ a.toNat ∧
        (D (panByteAlignHOL a) → LQ s.locals)) :
    AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR (.storeByte d v) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,hlo,hq⟩ := hd s aw pre
  have ne : w ≠ panByteAlignHOL a := by
    intro e; have := align_toNat a; rw [← e] at this; omega
  obtain ⟨res,_,loc,glob,_,_,_⟩ := evaluate_storeByte_control_frame s d v
  refine ⟨evaluate_storeByte_memory_frame s d v a w ha ne,fun _ => by rw [glob]; exact aw,
    fun e => ⟨by rw [loc]; exact sl,_,by rw [glob]; rfl,by
      rw [loc]; exact hq (dom.2.1 ▸ storeByte_none_dom' s d v a ha e)⟩,?_,?_,?_⟩
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

/-- A word store at or above `Lo` keeps every word below `Lo`; a normal outcome learns the address is in the domain. -/
theorem r_stw {LP LQ : GA → Prop} (Lo : BitVec 64) (hw : w.toNat < Lo.toNat) (d v : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals →
      ∃ a : BitVec 64, EV s d = some (.val (.word a)) ∧ Lo.toNat ≤ a.toNat ∧ (D a → LQ s.locals))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, A s.globals → LP s.locals → SL Vn s.locals →
      EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) :
    AQGD D B A w Vn (fun L _ _ => LP L) (fun L _ _ => LQ L) RR (.store d v) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  obtain ⟨a,ha,hlo,hq⟩ := hd s aw pre
  have ne : w ≠ a := by intro e; subst e; omega
  obtain ⟨res,_,loc,glob,mem⟩ := evaluate_store_word_frame s d v a ha (hv s · aw pre sl)
  refine ⟨mem w ne,fun _ => by rw [glob]; exact aw,fun e => ⟨by rw [loc]; exact sl,_,by unfold GIs; rw [glob],by
      rw [loc]; exact hq (dom.2.1 ▸ store_none_dom s d v a ha (hv s · aw pre sl) e)⟩,?_,?_,?_⟩
  · intro v' e; rcases res with h | h <;> rw [h] at e <;> cases e
  all_goals rcases res with h | h <;> rw [h] <;> simp

#print axioms r_stb
#print axioms r_stw
end st
def beLenBody : ProgHOL 64 :=
  ProgHOL.dec (ofString "n") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "v")) (ExpHOL.const 0#64)) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "v") (ExpHOL.shift Shift.lsr (ExpHOL.var VarKind.local (ofString "v")) (ExpHOL.const 8#64))) (ProgHOL.assign VarKind.local (ofString "n") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "n"), ExpHOL.const 1#64])))) (ProgHOL.return (ExpHOL.var VarKind.local (ofString "n"))))

theorem ushr_64 (x : BitVec 64) : x >>> 64 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight]
  have := x.isLt
  omega

theorem beLenBody_eq : sourceFunctionBody Guest.guestFn_rlp_be_len = beLenBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_be_len,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

section bl
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}

/-- `rlp_be_len(v)` returns at most 8. -/
theorem beLen_spec (V0 : BitVec 64) :
    AQGD D B A w Vn (fun L _ _ => L.lookup (ofString "v") = some (.val (.word V0))) (fun _ _ _ => False)
      (fun r _ _ => ∃ n : BitVec 64, r = .val (.word n) ∧ n.toNat ≤ 8) beLenBody := by
  unfold beLenBody
  let LI := fun L : GA => ∃ V N : BitVec 64, L.lookup (ofString "v") = some (.val (.word V)) ∧
    L.lookup (ofString "n") = some (.val (.word N)) ∧ N.toNat ≤ 8 ∧ V = V0 >>> (8 * N.toNat)
  refine r_dec (LB := LI) (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ hv ev
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨V0,0,by rw [lookup_update_ne' _ _ (by decide)]; exact hv,lookup_update_eq' _ _ _,by simp,by simp⟩
  refine aqgd_seq (r_while (LC := fun L => ∃ V : BitVec 64, L.lookup (ofString "v") = some (.val (.word V)) ∧ V ≠ 0)
    _ ?_ (aqgd_seq (r_assign (LQ := fun L => ∃ V N : BitVec 64, L.lookup (ofString "v") = some (.val (.word V)) ∧
      L.lookup (ofString "n") = some (.val (.word N)) ∧ N.toNat < 8 ∧ V = V0 >>> (8 * (N.toNat + 1))) _ _ ?_)
      (r_assign _ _ ?_))) (aqgd_return _ ?_)
  · intro F s x _ ⟨V,N,hv,_,_,_⟩ ev nz
    simp [EV,evalHOLExact,hv,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨V,hv,fun e => ?_⟩
    subst e; simp at ev; exact nz ev.symm
  · intro F s v _ ⟨⟨V,N,hv,hn,hle,hV⟩,V',hv',nz⟩ ev
    rw [hv] at hv'; simp at hv'; subst hv'
    simp [EV,evalHOLExact,hv,wordShiftHOL] at ev; subst ev
    have hlt : N.toNat < 8 := by
      by_contra h
      have : N.toNat = 8 := by omega
      rw [this] at hV
      apply nz; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hV
      simp [BitVec.toNat_ushiftRight] at this
      have h0 := V0.isLt
      rw [this]; simp [Nat.shiftRight_eq_div_pow]; omega
    refine ⟨_,N,lookup_update_eq' _ _ _,by rw [lookup_update_ne' _ _ (by decide)]; exact hn,hlt,?_⟩
    subst hV
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul,← pow_add]
    congr 2
  · intro F s v _ ⟨V,N,hv,hn,hlt,hV⟩ ev
    simp [EV,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (N + 1).toNat = N.toNat + 1 := by simp [BitVec.toNat_add]; omega
    exact ⟨V,N + 1,by rw [lookup_update_ne' _ _ (by decide)]; exact hv,lookup_update_eq' _ _ _,by omega,by rw [e1]; exact hV⟩
  · intro F s v _ _ _ ⟨V,N,_,hn,hle,_⟩ _ ev
    simp [EV,evalHOLExact,hn] at ev; subst ev
    exact ⟨N,rfl,hle⟩

#print axioms beLen_spec
end bl
def putBeBody : ProgHOL 64 :=
  ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.var VarKind.local (ofString "n")) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.const 0#64) (ExpHOL.var VarKind.local (ofString "i"))) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])) (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.var VarKind.local (ofString "v"))) (ProgHOL.assign VarKind.local (ofString "v") (ExpHOL.shift Shift.lsr (ExpHOL.var VarKind.local (ofString "v")) (ExpHOL.const 8#64)))))) (ProgHOL.return (ExpHOL.const 0#64)))

theorem putBeBody_eq : sourceFunctionBody Guest.guestFn_rlp_put_be = putBeBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_put_be,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- The domain fence: every domain address lies below `DF`. -/
def Fence (D : BitVec 64 → Prop) (DF : Nat) : Prop := ∀ a, D a → a.toNat < DF

theorem fence_byte {D : BitVec 64 → Prop} {DF : Nat} (hF : Fence D DF) {a : BitVec 64} (h : D (panByteAlignHOL a)) :
    a.toNat < DF + 8 := by
  have := hF _ h; rw [align_toNat] at this; omega

section pb
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop} {DF : Nat}

/-- `rlp_put_be(dst, v, n)` with `n ≤ 8` writes only `[dst, dst+n)`; a return knows `dst + n ≤ DF + 8` (when
`n > 0`). -/
theorem putBe_win (hF : Fence D DF) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat)
    (Dst N : BitVec 64) (hDst : Lo.toNat ≤ Dst.toNat) (hfit : Dst.toNat + 8 < 2 ^ 64) (hN : N.toNat ≤ 8) :
    AQGD D B A w Vn (fun L _ _ => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
        L.lookup (ofString "n") = some (.val (.word N))) (fun _ _ _ => False)
      (fun _ _ _ => N.toNat = 0 ∨ Dst.toNat + N.toNat ≤ DF + 8) putBeBody := by
  unfold putBeBody
  let LI := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
    ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat ∧
      (I.toNat < N.toNat → Dst.toNat + N.toNat ≤ DF + 8)
  refine r_dec (LB := LI) (LQ' := fun _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ⟨hd,hn⟩ ev
    simp [EV,evalHOLExact,hn] at ev; subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,N,lookup_update_eq' _ _ _,le_refl _,fun h => absurd h (by omega)⟩
  refine aqgd_seq (Q := fun L _ _ => LI L ∧ L.lookup (ofString "i") = some (.val (.word 0)))
    (aqgd_whileE (I := fun L _ _ => LI L)
      (C := fun L _ _ => ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ 0 < I.toNat)
      (E := fun L _ _ => L.lookup (ofString "i") = some (.val (.word 0))) (Qb := fun _ _ _ => False) _ ?_ ?_
      (aqgb_of_aqgd ?_) |> fun h => aqgd_conseq h (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h))
    (aqgd_return _ ?_)
  · intro F s x _ _ ⟨_,I,hi,_⟩ _ ev nz
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    refine ⟨I,hi,?_⟩
    by_cases h : (0#64 : BitVec 64) < I
    · simpa [BitVec.lt_def] using h
    · simp [h] at ev; exact absurd ev.symm nz
  · intro F s x _ _ ⟨_,I,hi,_⟩ _ ev z
    simp [EV,evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at ev
    have e : I = 0#64 := by
      by_cases h : (0#64 : BitVec 64) < I
      · simp [h] at ev; subst z; exact absurd ev (by decide)
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.lt_def] at h; simpa using h
    rw [e] at hi; exact hi
  · -- loop body: i = i - 1; st8 dst + i, v; v = v >>> 8
    let LJ := fun L : GA => L.lookup (ofString "dst") = some (.val (.word Dst)) ∧
      ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat < N.toNat ∧
        (I.toNat + 1 < N.toNat → Dst.toNat + N.toNat ≤ DF + 8)
    refine aqgd_seq (r_assign (LQ := LJ) _ _ ?_) (aqgd_seq (r_stb (LP := LJ) (LQ := LI) Lo hLo8 hw _ _ ?_)
      (r_assign _ _ ?_))
    · intro F s v _ ⟨⟨hd,I,hi,hle,hb⟩,I',hi',pos⟩ ev
      rw [hi] at hi'; simp at hi'; subst hi'
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      have e1 : (I - 1).toNat = I.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,I - 1,lookup_update_eq' _ _ _,by omega,
        fun h => hb (by omega)⟩
    · intro F s _ ⟨hd,I,hi,hlt,hb⟩
      refine ⟨Dst + I,by simp [EV,evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord],?_,?_⟩
      · have : (Dst + I).toNat = Dst.toNat + I.toNat := by simp [BitVec.toNat_add]; omega
        omega
      · intro hD
        have hb8 := fence_byte hF hD
        have : (Dst + I).toNat = Dst.toNat + I.toNat := by simp [BitVec.toNat_add]; omega
        exact ⟨hd,I,hi,by omega,fun _ => by
          by_cases h : I.toNat + 1 < N.toNat
          · exact hb h
          · omega⟩
    · intro F s v _ ⟨hd,I,hi,hle,hb⟩ _
      exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact hd,I,
        by rw [lookup_update_ne' _ _ (by decide)]; exact hi,hle,hb⟩
  · intro F s v _ _ _ ⟨⟨_,I,hi,hle,hb⟩,hz⟩ _ _
    rw [hi] at hz; simp at hz; subst hz
    by_cases h : N.toNat = 0
    · exact Or.inl h
    · exact Or.inr (hb (by simp; omega))

#print axioms putBe_win
end pb
end InitECandidate.Runtime
