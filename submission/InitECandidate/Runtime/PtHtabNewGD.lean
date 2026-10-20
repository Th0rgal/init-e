import InitECandidate.Runtime.PtSegTxhGD
/-!
The actual `htab_new(key_len, cap)` (whole-memory form, pinned-journal arena): from heap pointer `H` it returns `H`,
keeps every word below `H` and every global but `heap_ptr`, and leaves at `H` a nine-word header
`key_len, stride, cap, 0, keys, vals, used, order, order_pos` whose five arrays (8-aligned keys/used) lie in
`[H + 72, H')`, where `H' ≤ HEAP_END` is the exit heap pointer (`NewTab`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Header cells `T + off = val`. -/
def CellsAt (T : BitVec 64) (cells : List (BitVec 64 × BitVec 64)) (M : Mem) : Prop :=
  ∀ p ∈ cells, M (T + p.1) = .word p.2

theorem cellsAt_cons {T k y : BitVec 64} {cells : List (BitVec 64 × BitVec 64)} {M : Mem} (h : CellsAt T cells M)
    (hk : ∀ p ∈ cells, p.1 ≠ k) : CellsAt T ((k,y) :: cells) (fun x => if x = T + k then .word y else M x) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp
  · have : T + p.1 ≠ T + k := fun e => hk p hp (by simpa using e)
    simp only [this,if_false]
    exact h p hp

theorem cellsAt_frame {T : BitVec 64} {cells : List (BitVec 64 × BitVec 64)} {M M' : Mem} (h : CellsAt T cells M)
    (keep : ∀ p ∈ cells, M' (T + p.1) = M (T + p.1)) : CellsAt T cells M' :=
  fun p hp => (keep p hp).trans (h p hp)

/-- The fresh table left by `htab_new` at `H` with exit heap pointer `H'`. -/
def NewTab (H H' KL Cp : BitVec 64) (M : Mem) : Prop :=
  ∃ KS VS US OS OPS : BitVec 64,
    Hdr M H KL ((KL + 7#64) &&& (0#64 - 8#64)) Cp 0#64 KS VS US OS OPS ∧ KS.toNat % 8 = 0 ∧ US.toNat % 8 = 0 ∧
    H.toNat + 72 ≤ KS.toNat ∧ KS.toNat + (Cp * ((KL + 7#64) &&& (0#64 - 8#64))).toNat ≤ H'.toNat ∧
    H.toNat + 72 ≤ VS.toNat ∧ VS.toNat + (Cp * 8#64).toNat ≤ H'.toNat ∧
    H.toNat + 72 ≤ US.toNat ∧ US.toNat + Cp.toNat ≤ H'.toNat ∧
    H.toNat + 72 ≤ OS.toNat ∧ OS.toNat + (Cp * 8#64).toNat ≤ H'.toNat ∧
    H.toNat + 72 ≤ OPS.toNat ∧ OPS.toNat + (Cp * 8#64).toNat ≤ H'.toNat

section al
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- `allocN_spec` with the 8-alignment of the returned pointer. -/
theorem allocNA_spec (Nn H : BitVec 64) (M0 : Mem) (Gk : GA) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => (L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0 ∧ HeapIs G H) ∧ G = Gk)
      (fun _ _ _ => True)
      (fun v M' G' => (v = .val (.word H) ∧ M' = M0 ∧ H.toNat % 8 = 0 ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        H.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ OnlyHeap Gk G')
      (sourceFunctionBody Guest.guestFn_alloc) := by
  have hr : ReturnedRel (fun g g' => OnlyHeap g g') (sourceFunctionBody Guest.guestFn_alloc) := by
    have := alloc_returnedRel
    unfold ReturnedRel at this ⊢
    intro F s p v code e; exact (this s p v code e).1
  refine aqgd_conseq (aqgd_addRet hr ?_ Gk) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_jwsn (keepsJournalN_of_installed originalRuntimeCode_allocation_lookup (by decide)) ?_
  refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
    originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
    (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) Nn H M0)))
    (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
  · intro L M G ⟨⟨hl,hM,hH⟩,hn⟩
    exact ⟨hn,H,hH,hl,hM,rfl⟩
  · intro v M' G' ⟨_,H',hH',hM,ev,_,_,c1,c2,_,al⟩
    exact ⟨ev,hM,al,H',hH',c1,c2⟩

#print axioms allocNA_spec

/-- The heap pointer of a globals map (0 if absent). -/
def hpOf (G : GA) : BitVec 64 := wordOf G (ofString "heap_ptr")

theorem hpOf_eq {G : GA} {H : BitVec 64} (h : HeapIs G H) : hpOf G = H := wordOf_eq h

theorem onlyHeap_trans {g1 g2 g3 : GA} (h1 : OnlyHeap g1 g2) (h2 : OnlyHeap g2 g3) : OnlyHeap g1 g3 :=
  fun n hn => (h2 n hn).trans (h1 n hn)

theorem lk_update' {ps : List (MlS × BitVec 64)} {L : GA} (h : LK ps L) (name : MlS) (X : BitVec 64)
    (hn : ∀ p ∈ ps, p.1 ≠ name) : LK ((name,X) :: ps) (L.update (name,.val (.word X))) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact lookup_update_eq' _ _ _
  · exact lk_update h name _ hn p hp

/-- State inside `htab_new` from entry heap `H`: word locals `ps`, every word below `H` as in `M0`, header cells
`cells` at `Tt`, heap pointer at least `lo`, only `heap_ptr` changed since `Gk`. -/
def HNS (H Tt : BitVec 64) (M0 : Mem) (Gk : GA) (ps : List (MlS × BitVec 64))
    (cells : List (BitVec 64 × BitVec 64)) (lo : Nat) (L : GA) (M : Mem) (G : GA) : Prop :=
  LK ps L ∧ (∀ x, x.toNat < H.toNat → M x = M0 x) ∧ CellsAt Tt cells M ∧
    (∃ Hc : BitVec 64, HeapIs G Hc ∧ lo ≤ Hc.toNat) ∧ OnlyHeap Gk G

/-- `name = alloc(e)` inside `htab_new`: the new block `X` is 8-aligned, at least `lo`, and `X + N ≤ HEAP_END`. -/
theorem hn_allocStep {H Tt : BitVec 64} {M0 : Mem} {Gk : GA} {ps : List (MlS × BitVec 64)}
    {cells : List (BitVec 64 × BitVec 64)} {lo : Nat} {RR : ValueHOL 64 → Mem → GA → Prop} (name : MlS)
    (e : ExpHOL 64) (Nn : BitVec 64) {cont : ProgHOL 64}
    (hev : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LK ps s.locals → EV s e = some (.val (.word Nn)))
    (hname : ∀ p ∈ ps, p.1 ≠ name)
    (hcont : ∀ X : BitVec 64, X.toNat % 8 = 0 → lo ≤ X.toNat → X.toNat + Nn.toNat ≤ 33806089496 →
      AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
        (HNS H Tt M0 Gk ((name,X) :: ps) cells (X.toNat + Nn.toNat)) (fun _ _ _ => False) RR cont) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (HNS H Tt M0 Gk ps cells lo) (fun _ _ _ => False) RR
      (.decCall name .one (ofString "alloc") [e] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0' ∧ HeapIs G (hpOf G0')) ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      (v = .val (.word (hpOf G0')) ∧ M' = M0' ∧ (hpOf G0').toNat % 8 = 0 ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        (hpOf G0').toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ OnlyHeap G0' G')
    (Pc := fun L M G => ∃ X : BitVec 64, HNS H Tt M0 Gk ((name,X) :: ps) cells (X.toNat + Nn.toNat) L M G ∧
      (X.toNat % 8 = 0 ∧ lo ≤ X.toNat ∧ X.toNat + Nn.toNat ≤ 33806089496))
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' G0' _ => allocNA_spec (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
      (Nj := Nj) (D := D) (B := B) (w := w) Nn (hpOf G0') M0' G0') ?_ (fun _ => rfl) ?_
    (aqgd_exE (fun X => aqgd_pureE (fun ⟨a,b,c⟩ => hcont X a b c))) (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ H' hG ⟨lk,_,_,⟨Hc,hHc,_⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    rw [hev s lk] at ex
    simp only [Option.some.injEq] at ex; subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,by rw [hpOf_eq hHc]; exact hHc⟩,rfl⟩
  · intro L M G v M' G' ⟨lk,fr,ce,⟨Hc,hHc,le⟩,oh⟩ ⟨⟨ev,eM,al,H',hH',c1,c2⟩,oh'⟩ _
    subst ev eM
    rw [hpOf_eq hHc] at al c1 ⊢
    exact ⟨Hc,⟨lk_update' lk name _ hname,fr,ce,⟨H',hH',c1⟩,onlyHeap_trans oh oh'⟩,al,le,by omega⟩

#print axioms hn_allocStep

/-- A header store `st t + k, v` (word value `y`, `k < 72`) inside `htab_new`. -/
theorem hn_storeStep {H Tt : BitVec 64} {M0 : Mem} {Gk : GA} {ps : List (MlS × BitVec 64)}
    {cells : List (BitVec 64 × BitVec 64)} {lo : Nat} {RR : ValueHOL 64 → Mem → GA → Prop} (k y : BitVec 64)
    (v : ExpHOL 64) (hk : k.toNat < 72) (hT : Tt.toNat + 72 ≤ 33806089496) (hHT : H.toNat ≤ Tt.toNat)
    (hw : w.toNat < H.toNat) (ht : ∀ L, LK ps L → L.lookup (ofString "t") = some (.val (.word Tt)))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LK ps s.locals → EV s v = some (.val (.word y)))
    (hnew : ∀ p ∈ cells, p.1 ≠ k) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (HNS H Tt M0 Gk ps cells lo)
      (HNS H Tt M0 Gk ps ((k,y) :: cells) lo) RR (.store (.op .add [.var .local (ofString "t"),.const k]) v) := by
  have e : (Tt + k).toNat = Tt.toNat + k.toNat := by simp [BitVec.toNat_add]; omega
  refine aqgd_storeD _ _ (fun s G _ _ hG ⟨lk,fr,ce,hh,oh⟩ _ => ?_)
    (fun s x _ _ _ _ pre _ ev => ⟨y,by rw [hv s pre.1] at ev; exact (Option.some.inj ev).symm⟩)
  unfold GIs at hG; subst hG
  refine ⟨Tt + k,ev_addc s _ Tt k (ht _ lk),fun h => by rw [← h] at e; omega,fun y' ev' => ?_⟩
  rw [hv s lk] at ev'
  have hy := (Option.some.inj ev').symm
  simp only [ValueHOL.val.injEq,HolWordLab.word.injEq] at hy
  subst hy
  refine ⟨lk,fun x hx => ?_,cellsAt_cons ce hnew,hh,oh⟩
  have : x ≠ Tt + k := fun h => by rw [← h] at e; omega
  simp only [this,if_false]; exact fr x hx

#print axioms hn_storeStep

/-- `memzero(used, cap)` inside `htab_new`: the used array lies at or above `Tt + 72`. -/
theorem hn_memzeroStep {H Tt : BitVec 64} {M0 : Mem} {Gk : GA} {ps : List (MlS × BitVec 64)}
    {cells : List (BitVec 64 × BitVec 64)} {lo : Nat} {RR : ValueHOL 64 → Mem → GA → Prop} (US Cp : BitVec 64)
    (hU : ∀ L, LK ps L → L.lookup (ofString "used") = some (.val (.word US)))
    (hC : ∀ L, LK ps L → L.lookup (ofString "cap") = some (.val (.word Cp)))
    (hal : US.toNat % 8 = 0) (hlo : Tt.toNat + 72 ≤ US.toNat) (hfit : US.toNat + Cp.toNat ≤ 33806089496)
    (hHT : H.toNat ≤ Tt.toNat) (hcells : ∀ p ∈ cells, p.1.toNat < 72) (hw : w.toNat < H.toNat) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True) (HNS H Tt M0 Gk ps cells lo)
      (HNS H Tt M0 Gk ps cells lo) RR
      (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "used"),.var .local (ofString "cap")]) := by
  have below : ∀ x : BitVec 64, x.toNat < US.toNat → ¬ MWin US Cp.toNat x :=
    fun x hx => mwin_belowS hal (by omega) hx
  refine aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (L.lookup (ofString "dst") = some (.val (.word US)) ∧ L.lookup (ofString "n") = some (.val (.word Cp))) ∧
        M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      G' = G0' ∧ ∀ x, ¬ MWin US Cp.toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp)
    (fun _ M0' G0' _ => memzero_wn US Cp (by omega) (below w (by omega)) M0' G0') ?_ ?_
  · intro F s values callee rs _ H' hG ⟨lk,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    simp [EV,evalHOLExact,hU _ lk] at ev1; subst ev1
    simp [EV,evalHOLExact,hC _ lk] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_memzero_lookup lookup
    exact ⟨⟨by rw [e]; simp (config := {decide := true}),by rw [e]; simp (config := {decide := true})⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lk,fr,ce,hh,oh⟩ ⟨hG,fz⟩
    subst hG
    refine ⟨lk,fun x hx => (fz x (below x (by omega))).trans (fr x hx),
      cellsAt_frame ce (fun p hp => fz _ (below _ ?_)),hh,oh⟩
    have := hcells p hp
    have : (Tt + p.1).toNat = Tt.toNat + p.1.toNat := by simp [BitVec.toNat_add]; omega
    omega

#print axioms hn_memzeroStep

/-- The actual `htab_new(key_len, cap)` from heap pointer `H`: returns a table `Tt ≥ H` (`NewTab`), keeps every word
below `H`, changes only `heap_ptr`, and ends with heap pointer `H' ≤ HEAP_END`, `Tt + 72 ≤ H'`. -/
theorem htabNew_spec (KL Cp H : BitVec 64) (hw : w.toNat < H.toNat) (M0 : Mem) (Gk : GA) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => (LK [(ofString "cap",Cp),(ofString "key_len",KL)] L ∧ M = M0 ∧ HeapIs G H) ∧ G = Gk)
      (fun _ _ _ => False)
      (fun v M' G' => ∃ Tt : BitVec 64, v = .val (.word Tt) ∧ H.toNat ≤ Tt.toNat ∧
        (∀ x, x.toNat < H.toNat → M' x = M0 x) ∧ OnlyHeap Gk G' ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
          Tt.toNat + 72 ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ NewTab Tt H' KL Cp M')
      (sourceFunctionBody Guest.guestFn_htab_new) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_htab_new,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  let SD : BitVec 64 := (KL + 7#64) &&& (0#64 - 8#64)
  refine aqgd_conseq (P := HNS H H M0 Gk [(ofString "cap",Cp),(ofString "key_len",KL)] [] H.toNat) ?_
    (fun L M G ⟨⟨lk,hM,hH⟩,hG⟩ => by subst hM hG; exact ⟨lk,fun _ _ => rfl,fun p hp => by simp at hp,⟨H,hH,le_refl _⟩,
      fun _ _ => rfl⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- t = alloc(72)
  refine hn_allocStep (ofString "t") (.const 72) 72#64 (fun s _ => by simp [EV,evalHOLExact])
    (by simp (config := {decide := true})) (fun Tt alT loT fitT => ?_)
  refine aqgd_conseq (P := HNS H Tt M0 Gk [(ofString "t",Tt),(ofString "cap",Cp),(ofString "key_len",KL)] []
    (Tt.toNat + (72#64).toNat)) ?_ (fun L M G h => ⟨h.1,h.2.1,fun p hp => by simp at hp,h.2.2.2⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  have h72 : (72#64).toNat = 72 := rfl
  -- stride
  refine aqgd_dec (Pb := HNS H Tt M0 Gk [(ofString "stride",SD),(ofString "t",Tt),(ofString "cap",Cp),
      (ofString "key_len",KL)] [] (Tt.toNat + 72)) (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl)
    (fun s v _ _ _ ⟨lk,fr,ce,hh,oh⟩ _ ev _ => ?_) ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · have hk : s.locals.lookup (ofString "key_len") = some (.val (.word KL)) := lk (ofString "key_len",KL) (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,hk,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨lk_update' lk _ _ (by simp (config := {decide := true})),fr,ce,by rw [h72] at hh; exact hh,oh⟩
  have hHT : H.toNat ≤ Tt.toNat := by omega
  have hT : Tt.toNat + 72 ≤ 33806089496 := by rw [h72] at fitT; exact fitT
  refine aqgd_seq (hn_storeStep 0#64 KL _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "key_len",KL) (by simp)]) (by simp)) ?_
  refine aqgd_seq (hn_storeStep 8#64 SD _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "stride",SD) (by simp)]) (by simp)) ?_
  refine aqgd_seq (hn_storeStep 16#64 Cp _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "cap",Cp) (by simp)]) (by simp)) ?_
  refine aqgd_seq (hn_storeStep 24#64 0#64 _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact]) (by simp)) ?_
  -- keys = alloc(cap * stride)
  refine hn_allocStep (ofString "keys") _ (Cp * SD) (fun s lk => by
      simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "cap",Cp) (by simp),lk (ofString "stride",SD) (by simp),
        panOpHOL,valueIsWord,valueWord]) (by simp (config := {decide := true})) (fun KS alK loK fitK => ?_)
  refine aqgd_seq (hn_storeStep 32#64 KS _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "keys",KS) (by simp)]) (by simp)) ?_
  -- vals = alloc(cap * 8)
  refine hn_allocStep (ofString "vals") _ (Cp * 8#64) (fun s lk => by
      simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "cap",Cp) (by simp),panOpHOL,valueIsWord,valueWord])
    (by simp (config := {decide := true})) (fun VS alV loV fitV => ?_)
  refine aqgd_seq (hn_storeStep 40#64 VS _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "vals",VS) (by simp)]) (by simp)) ?_
  -- used = alloc(cap); memzero(used, cap)
  refine hn_allocStep (ofString "used") _ Cp (fun s lk => by
      simp [EV,evalHOLExact,lk (ofString "cap",Cp) (by simp)])
    (by simp (config := {decide := true})) (fun US alU loU fitU => ?_)
  refine aqgd_seq (hn_memzeroStep US Cp (fun L lk => lk (ofString "used",US) (by simp))
    (fun L lk => lk (ofString "cap",Cp) (by simp)) alU (by omega) fitU hHT (by simp) hw) ?_
  refine aqgd_seq (hn_storeStep 48#64 US _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "used",US) (by simp)]) (by simp)) ?_
  -- order = alloc(cap * 8)
  refine hn_allocStep (ofString "order") _ (Cp * 8#64) (fun s lk => by
      simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "cap",Cp) (by simp),panOpHOL,valueIsWord,valueWord])
    (by simp (config := {decide := true})) (fun OS alO loO fitO => ?_)
  refine aqgd_seq (hn_storeStep 56#64 OS _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "order",OS) (by simp)]) (by simp)) ?_
  -- order_pos = alloc(cap * 8)
  refine hn_allocStep (ofString "order_pos") _ (Cp * 8#64) (fun s lk => by
      simp [EV,evalHOLExact,evalListHOLExact,lk (ofString "cap",Cp) (by simp),panOpHOL,valueIsWord,valueWord])
    (by simp (config := {decide := true})) (fun OPS alP loP fitP => ?_)
  refine aqgd_seq (hn_storeStep 64#64 OPS _ (by decide) hT hHT hw (fun L lk => lk (ofString "t",Tt) (by simp))
    (fun s lk => by simp [EV,evalHOLExact,lk (ofString "order_pos",OPS) (by simp)]) (by simp)) ?_
  -- return t
  refine aqgd_return _ (fun s v G' aw hG ⟨lk,fr,ce,⟨Hc,hHc,le⟩,oh⟩ _ ev => ?_)
  unfold GIs at hG; subst hG
  simp [EV,evalHOLExact,lk (ofString "t",Tt) (by simp)] at ev
  subst ev
  have hcap := (jws_heap_facts aw.1 hHc).2.1
  have eSD : (Cp * SD).toNat = (Cp * ((KL + 7#64) &&& (0#64 - 8#64))).toNat := rfl
  exact ⟨Tt,rfl,hHT,fr,oh,Hc,hHc,by omega,hcap,KS,VS,US,OS,OPS,
    ⟨ce (0#64,KL) (by simp),ce (8#64,SD) (by simp),ce (16#64,Cp) (by simp),ce (24#64,0#64) (by simp),
      ce (32#64,KS) (by simp),ce (40#64,VS) (by simp),ce (48#64,US) (by simp),ce (56#64,OS) (by simp),
      ce (64#64,OPS) (by simp)⟩,alK,alU,by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega⟩

#print axioms htabNew_spec
end al
end InitECandidate.Runtime
