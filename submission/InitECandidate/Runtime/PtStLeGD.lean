import InitECandidate.Runtime.PtWsReadCGD
import InitECandidate.Runtime.RecBeStoreGD
import InitECandidate.Runtime.OriginalStoreLE32Code
import InitECandidate.Runtime.OriginalStoreLE64Code
/-!
Whole-memory frames from per-watched-word triples (`aqgd_frameAll`, the instance-per-word trick), a globals-keeping
wrapper for bodies passing the whole-program `keepsGA` check (`aqgd_keepGA`), and the actual little-endian stores
`st_le32(p, v)` / `st_le64(p, v)` writing only `[P, P + 4)` / `[P, P + 8)`, with the `st_le64` call statement.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section fa
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- Per-watched-word triples outside a window give the whole-memory frame outside it in the posts. -/
theorem aqgd_frameAll {Win : BitVec 64 → Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {M0 : Mem}
    (h : ∀ x, ¬ Win x → AQGD D B A x Vn (fun L M G => P L M G ∧ M = M0) Q RR p) (hw : ¬ Win w) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ M = M0) (fun L M G => Q L M G ∧ ∀ x, ¬ Win x → M x = M0 x)
      (fun v M G => RR v M G ∧ ∀ x, ¬ Win x → M x = M0 x) p := by
  intro F s code dom aw sl H hH pre
  have all := fun (x : BitVec 64) (hx : ¬ Win x) => h x hx F s code dom aw sl H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := all w hw
  have fr : ∀ x, ¬ Win x → (evaluateHOLFiniteState s p).2.memory x = M0 x := fun x hx => by
    rw [(all x hx).1,pre.2]
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',hH',q⟩ := n e
    exact ⟨sl',H',hH',q,fr⟩
  · obtain ⟨H',hH',q⟩ := r v e
    exact ⟨H',hH',q,fr⟩

#print axioms aqgd_frameAll

/-- A body passing the whole-program globals check keeps every global. -/
theorem aqgd_keepGA {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {G0 : GA} (hk : keepsGA goodGA p = true)
    (h : AQGD D B A w Vn P Q RR p) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ G = G0) (fun L M G => Q L M G ∧ G = G0)
      (fun v M G => RR v M G ∧ G = G0) p := by
  intro F s code dom aw sl H hH ⟨pre,hG⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  have keep := evaluate_keepsGA goodGA goodGA_bodies p hk s code
  unfold GIs at hH; subst hH
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',hH',q⟩ := n e
    unfold GIs at hH'; subst hH'
    exact ⟨sl',_,rfl,q,by rw [keep]; exact hG⟩
  · obtain ⟨H',hH',q⟩ := r v e
    unfold GIs at hH'; subst hH'
    exact ⟨_,rfl,q,by rw [keep]; exact hG⟩

#print axioms aqgd_keepGA
end fa

section le
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- `st_le32(p, v)` writes only `[P, P + 4)`. -/
theorem stLe32_wn (P : BitVec 64) (out : ¬ MWin P 4 w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P)))
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_st_le32) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_st_le32,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  have st : ∀ (j : Nat) (d v : ExpHOL 64), j < 4 → (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.locals.lookup (ofString "p") = some (.val (.word P)) → EV s d = some (.val (.word (P + BitVec.ofNat 64 j)))) →
      AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P)))
        (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P))) (fun _ _ _ => True) (.storeByte d v) :=
    fun j d v hj hd => aqgd_storeByte _ _ (fun s _ _ pre _ => ⟨_,hd s pre,fun e => out ⟨j,hj,Or.inr e⟩,
      fun _ _ => pre⟩)
  refine aqgd_seq (st 0 _ _ (by decide) (fun s hp => by simp [EV,evalHOLExact,hp])) ?_
  refine aqgd_seq (st 1 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  refine aqgd_seq (st 2 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  refine aqgd_seq (st 3 _ _ (by decide) (fun s hp => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,wordOpHOL,wordOp,valueIsWord,valueWord])) ?_
  exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)

#print axioms stLe32_wn

/-- `st_le64(p, v)` writes only `[P, P + 8)`. -/
theorem stLe64_wn (P : BitVec 64) (out : ¬ MWin P 8 w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "p") = some (.val (.word P)))
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_st_le64) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_st_le64,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  let LP := fun L : GA => L.lookup (ofString "p") = some (.val (.word P))
  refine aqgd_seq (aqgd_callWin (LP := LP) _ _ _ _ _ originalRuntimeCode_storeLE32_lookup (by simp)
    (fun _ L => L.lookup (ofString "p") = some (.val (.word P)))
    (fun _ _ M0 G0 => aqgd_conseq (stLe32_wn P (mwin_mono (by decide) out)) (fun _ _ _ h => h.1)
      (fun _ _ _ h => h) (fun _ _ _ h => h))
    (fun s values callee rs _ hp args lookup => entry_p originalRuntimeCode_storeLE32_lookup s _ _ P
      (by simp [EV,evalHOLExact,(show s.locals.lookup (ofString "p") = some (.val (.word P)) from hp)]) args lookup)) ?_
  refine aqgd_seq (aqgd_callWin (LP := LP) _ _ _ _ _ originalRuntimeCode_storeLE32_lookup (by simp)
    (fun _ L => L.lookup (ofString "p") = some (.val (.word (P + 4#64))))
    (fun _ _ M0 G0 => aqgd_conseq (stLe32_wn (P + 4#64) (mwin_shift out 4 4 (by decide))) (fun _ _ _ h => h.1)
      (fun _ _ _ h => h) (fun _ _ _ h => h))
    (fun s values callee rs _ hp args lookup => entry_p originalRuntimeCode_storeLE32_lookup s _ _ _
      (by simp [EV,evalHOLExact,evalListHOLExact,(show s.locals.lookup (ofString "p") = some (.val (.word P)) from hp),
        wordOpHOL,wordOp,valueIsWord,valueWord]) args lookup)) ?_
  exact aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)

#print axioms stLe64_wn

/-- The actual `st_le64(ep, ev)` call statement: globals unchanged, memory outside `[P, P + 8)` unchanged. -/
theorem aqgd_call_stLe64 {LP : GA → Prop} (ep ev : ExpHOL 64) (P : BitVec 64) (M1 : Mem) (G1 : GA)
    (out : ¬ MWin P 8 w)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memory = M1 → s.globals = G1 → LP s.locals →
      EV s ep = some (.val (.word P))) :
    AQGD D B A w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1)
      (fun L M G => LP L ∧ G = G1 ∧ ∀ x, ¬ MWin P 8 x → M x = M1 x) RR
      (.call (some (none,none)) (ofString "st_le64") [ep,ev]) := by
  refine aqgd_callSpecS (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "p") = some (.val (.word P)) ∧ M = M0') ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => ((∀ x, ¬ MWin P 8 x → M' x = M0' x)) ∧ G' = G0')
    _ _ _ _ _ originalRuntimeCode_storeLE64_lookup (fun _ _ _ _ _ h => h.elim) ?_ ?_ ?_
  · intro L0 M0' G0' _
    refine aqgd_conseq (aqgd_keepGA (Q := fun _ _ _ => True) (keepsGA_of_installed originalRuntimeCode_storeLE64_lookup
      (by decide)) ?_) (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_frameAll (Win := MWin P 8) (fun x hx => aqgd_conseq (stLe64_wn (w := x) P hx)
      (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) out) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h.2)
  · intro F s values callee rs _ H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    exact ⟨⟨entry_p originalRuntimeCode_storeLE64_lookup s _ _ P (hp s hM hG1 lp) args lookup,rfl⟩,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨fr,eG⟩
    subst hM hG
    exact ⟨lp,eG,fr⟩

#print axioms aqgd_call_stLe64
end le
end InitECandidate.Runtime
