import InitECandidate.Runtime.PtSegBaseGD
import InitECandidate.Runtime.OriginalPtSegCode
/-!
The actual zeroed-block constructors `te_new()` (`alloc(200)`, `memzero`) and `msg_new()` (`alloc(176)`, `memzero`):
the returned block is the entry heap pointer `H`, only `[H, H + N)` is written, the heap pointer ends at or above
`H + N`, and only `heap_ptr` changes; the call site keeps the segment state `SI` (the block lies at or above `Lo`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- `x = alloc(N); memzero(x, N); return x`. -/
def newBlkBody (x : MlS) (Nn : BitVec 64) : ProgHOL 64 :=
  .decCall x .one (ofString "alloc") [.const Nn]
    (.seq (.call (some (none,none)) (ofString "memzero") [.var .local x,.const Nn]) (.return (.var .local x)))

theorem teNew_eq : sourceFunctionBody Guest.guestFn_te_new = newBlkBody (ofString "te") 200#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_te_new,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

theorem msgNew_eq : sourceFunctionBody Guest.guestFn_msg_new = newBlkBody (ofString "m") 176#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_msg_new,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

section nb
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- `newBlkBody x N` from heap pointer `H`: returns `H`, writes only `[H, H + N)`, heap at least `H + N`, only
`heap_ptr` changes. -/
theorem newBlk_spec (x : MlS) (Nn H : BitVec 64) (small : Nn.toNat + 32 < 2 ^ 64) (hw : ¬ MWin H Nn.toNat w)
    (M0 : Mem) (Gk : GA) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun _ M G => (M = M0 ∧ HeapIs G H) ∧ G = Gk) (fun _ _ _ => False)
      (fun v M' G' => (v = .val (.word H) ∧ (∀ y, ¬ MWin H Nn.toNat y → M' y = M0 y) ∧
        ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ OnlyHeap Gk G')
      (newBlkBody x Nn) := by
  unfold newBlkBody
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0' ∧ HeapIs G H) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word H) ∧ M' = M0' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧ H.toNat + Nn.toNat ≤ H'.toNat ∧
        H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L M G => (L.lookup x = some (.val (.word H)) ∧ M = M0 ∧ ∃ H' : BitVec 64, HeapIs G H' ∧
      H.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ OnlyHeap Gk G)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocN_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) Nn H M0' G0') ?_ (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨⟨_,hH⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨y,rfl,ey⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ey
    subst ey
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hH⟩,rfl⟩
  · intro L M G v M' G' ⟨⟨hM,_⟩,hG⟩ ⟨⟨ev,eM,H',hH',c1,c2⟩,oh⟩ _
    subst ev hG hM eM
    exact ⟨⟨lookup_update_eq' _ _ _,rfl,H',hH',c1,c2⟩,oh⟩
  refine aqgd_seq (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word H)) ∧ L.lookup (ofString "n") = some (.val (.word Nn))) ∧
        M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ y, ¬ MWin H Nn.toNat y → M' y = M0' y)
    (Q := fun L M' G => (L.lookup x = some (.val (.word H)) ∧ (∀ y, ¬ MWin H Nn.toNat y → M' y = M0 y) ∧
      ∃ H' : BitVec 64, HeapIs G H' ∧ H.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ OnlyHeap Gk G)
    _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp)
    (fun _ M0' G0' _ => memzero_wn H Nn small hw M0' G0') ?_ ?_) ?_
  · intro F s values callee rs _ H' hG ⟨⟨hx,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hx] at ev1; subst ev1
    simp [EV,evalHOLExact] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_memzero_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨hx,hM,hh⟩,oh⟩ ⟨hG,fr⟩
    subst hG hM
    exact ⟨⟨hx,fr,hh⟩,oh⟩
  · exact aqgd_return _ (fun s v _ _ hG ⟨⟨hx,fr,hh⟩,oh⟩ _ ev => by
      unfold GIs at hG; subst hG
      simp [EV,evalHOLExact,hx] at ev; subst ev
      exact ⟨⟨rfl,fr,hh⟩,oh⟩)

#print axioms newBlk_spec
end nb

section nbs
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Lo Nj : BitVec 64} {M0 : Mem}

/-- `name = f()` for an installed zeroed-block constructor `f` with body `newBlkBody x N`, keeping `SI`: the new local
is a block `Hb` at or above `Lo`, 8-aligned, ending at or below `HEAP_END`. -/
theorem aqgd_decCall_newBlk_si {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name fn x : MlS) (Nn : BitVec 64)
    {cont : ProgHOL 64} (installed : originalRuntimeCode.lookup fn = some ([],newBlkBody x Nn,.one))
    (smallN : Nn.toNat < 2 ^ 32) (hkBo : keepsG (ofString "bo") goodBo (newBlkBody x Nn) = true)
    (hkWs : keepsG (ofString "u256_ws") goodWs (newBlkBody x Nn) = true)
    (hkScr : keepsG (ofString "secp_accel_scratch") goodScr (newBlkBody x Nn) = true)
    (hw : w.toNat < Lo.toNat)
    (hup : ∀ L (Hb : BitVec 64), LP L → Lo.toNat ≤ Hb.toNat → Hb.toNat + Nn.toNat ≤ 33806089496 →
      Hb.toNat % 8 = 0 → LP' (L.update (name,.val (.word Hb))))
    (hcont : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP' L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) Q2 RR (.decCall name .one fn [] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ Hb : BitVec 64, HeapIs G0' Hb ∧ Hb.toNat % 8 = 0 ∧ Hb.toNat ≤ 33806089496 ∧
        (((v = .val (.word Hb) ∧ (∀ y, ¬ MWin Hb Nn.toNat y → M' y = M0' y) ∧
          ∃ H' : BitVec 64, HeapIs G' H' ∧ Hb.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧
            OnlyHeap G0' G') ∧ ScrIs Sc G') ∧ G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => LP' L ∧ SI n c T Out ko D B Excl Lo Nj M0 M G) (Qc := Q)
    _ _ _ _ _ _ _ installed (by simp) ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,⟨Hb,hH,hle⟩,_,hn,_⟩
    refine aqgd_of_arenaFact (Φ := (P0.toNat ≤ Hb.toNat ∧ Hb.toNat ≤ 33806089496 ∧ Hb.toNat % 8 = 0) ∧ ScrIs Sc G0')
      (fun _ _ g aw ⟨_,hg⟩ => by subst hg; exact ⟨jws_heap_facts aw.1.1.1 hH,aw.2⟩) ?_
    intro ⟨⟨_,hcapH,hal⟩,hsc⟩
    have hwb : ¬ MWin Hb Nn.toNat w := mwin_belowS hal (by omega) (by omega)
    have h1 := aqgd_conseq (aqgd_keepScr (Sc := Sc) hkScr (newBlk_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0)
      (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB) (Nj := Nj) x Nn Hb (by omega) hwb M0' G0'))
      (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo) hkBo hkWs h1) ?_ (fun _ _ _ h => h.elim) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨⟨⟨⟨rfl,hH⟩,rfl⟩,hsc⟩,hn⟩
    · intro v M' G' ⟨⟨rr,sc⟩,hn'⟩
      exact ⟨Hb,hH,hal,hcapH,⟨rr,sc⟩,hn'⟩
  · intro L M G v M' G' ⟨lp,si⟩ ⟨Hb,hH,hal,hcap,⟨⟨⟨ev,fr,H',hH',c1,c2⟩,_⟩,_⟩,hn'⟩ _
    subst ev
    obtain ⟨H1,hH1,le1⟩ := si.1
    have e := heapIs_unique hH1 hH
    subst e
    exact ⟨hup L H1 lp le1 (by omega) hal,
      si_glob (si_mem si (fun y hy => fr y (mwin_belowS hal (by omega) (by omega)))) ⟨H',hH',by omega⟩ hn'⟩

#print axioms aqgd_decCall_newBlk_si
end nbs
end InitECandidate.Runtime
