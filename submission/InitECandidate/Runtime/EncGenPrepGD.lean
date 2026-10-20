import InitECandidate.Runtime.EncAuthGD
/-!
Value specs of the actual `rlp_header_len` / `rlp_list_header_len` (at most 9), and cursor adapters for the
`tx_encode_generic` writers (`tx_put_to`, `tx_put_access_list`, `tx_put_blob_hashes`, and `tx_put_u256` /
`tx_put_authorizations` keeping "heap pointer at or above `H0`").
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hlBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notLower (ExpHOL.const 55#64) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.return (ExpHOL.const 1#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "ll") ShapeHOL.one (ofString "rlp_be_len") [ExpHOL.var VarKind.local (ofString "n")] (ProgHOL.return (ExpHOL.op BinOp.add [ExpHOL.const 1#64, ExpHOL.var VarKind.local (ofString "ll")])))

def lhlBody : ProgHOL 64 :=
  ProgHOL.call none (ofString "rlp_header_len") [ExpHOL.var VarKind.local (ofString "payload_len")]

theorem hlBody_eq : sourceFunctionBody Guest.guestFn_rlp_header_len = hlBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_header_len,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

theorem lhlBody_eq : sourceFunctionBody Guest.guestFn_rlp_list_header_len = lhlBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_rlp_list_header_len,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


section hl
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

/-- `rlp_header_len(n)` returns at most 9. -/
theorem headerLen_spec (Nn : BitVec 64) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "n") = some (.val (.word Nn))) (fun _ _ _ => False)
      (fun r _ _ => ∃ R : BitVec 64, r = .val (.word R) ∧ R.toNat ≤ 9) (sourceFunctionBody Guest.guestFn_rlp_header_len) := by
  rw [hlBody_eq]; unfold hlBody
  refine aqgd_seq (r_ite _ (aqgd_return _ (fun _ v _ _ _ _ _ ev => by
    simp [EV,evalHOLExact] at ev; subst ev; exact ⟨1,rfl,by simp⟩)) aqgd_skip) ?_
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) => L.lookup (ofString "v") = some (.val (.word Nn)))
    (RRe := fun (_ : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (_ : GA) =>
      ∃ n : BitVec 64, r = .val (.word n) ∧ n.toNat ≤ 8)
    (Pc := fun L _ _ => ∃ Lw : BitVec 64, L.lookup (ofString "ll") = some (.val (.word Lw)) ∧ Lw.toNat ≤ 8)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_rlpBeLen_lookup (by simp)
    (fun _ _ _ _ => by
      rw [beLenBody_eq]
      exact aqgd_conseq (beLen_spec Nn) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    ?_ (fun h => h.elim) ?_ (aqgd_return _ ?_) (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ hn _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hn] at args
    subst args
    have e := callee_eq originalRuntimeCode_rlpBeLen_lookup lookup
    rw [e]; simp
  · intro L _ _ r _ _ _ ⟨n,hr,hn⟩ _
    subst hr
    exact ⟨n,lookup_update_eq' _ _ _,hn⟩
  · intro F s v _ _ _ ⟨Lw,hl,hle⟩ _ ev
    simp [EV,evalHOLExact,evalListHOLExact,hl,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (1 + Lw).toNat = 1 + Lw.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨1 + Lw,rfl,by rw [e1]; omega⟩

/-- `rlp_list_header_len(payload_len)` returns at most 9. -/
theorem listHeaderLen_spec (PL : BitVec 64) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "payload_len") = some (.val (.word PL)))
      (fun _ _ _ => False) (fun r _ _ => ∃ R : BitVec 64, r = .val (.word R) ∧ R.toNat ≤ 9)
      (sourceFunctionBody Guest.guestFn_rlp_list_header_len) := by
  rw [lhlBody_eq]; unfold lhlBody
  exact aqgd_tailCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ _ => L.lookup (ofString "n") = some (.val (.word PL)))
    (RRe := fun _ _ _ r _ _ => ∃ R : BitVec 64, r = .val (.word R) ∧ R.toNat ≤ 9) _ _ _ _ _
    originalRuntimeCode_rlpHeaderLen_lookup (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => aqgd_conseq (headerLen_spec PL) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
    (fun s values callee rs _ _ _ hp _ args lookup => by
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,hp] at args
      subst args
      have e := callee_eq originalRuntimeCode_rlpHeaderLen_lookup lookup
      rw [e]; simp)
    (fun _ _ _ _ _ _ _ h => h)

/-- Callee entry of a three-parameter writer called as `f(p, e2, e3)` with word-valued `e2`, `e3`. -/
theorem hpe3g {f q2 q3 : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(ofString "dst",.one),(q2,.one),(q3,.one)],bd,rs0))
    (h2 : ofString "dst" ≠ q2) (h3 : ofString "dst" ≠ q3) (h23 : q2 ≠ q3)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (e2 e3 : ExpHOL 64) (P : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (he2 : ∀ v, EV s e2 = some v → ∃ y : BitVec 64, v = .val (.word y))
    (he3 : ∀ v, EV s e3 = some v → ∃ y : BitVec 64, v = .val (.word y)) {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),e2,e3] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    callee.lookup (ofString "dst") = some (.val (.word P)) ∧
      (∃ Y : BitVec 64, callee.lookup q2 = some (.val (.word Y))) ∧
      ∃ Y : BitVec 64, callee.lookup q3 = some (.val (.word Y)) := by
  obtain ⟨v1,vs,rfl,e1,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,e2',r2⟩ := evalList_cons' s _ _ _ r1
  obtain ⟨v3,vs3,rfl,e3',r3⟩ := evalList_cons' s _ _ _ r2
  have := evalList_nil' s _ r3; subst this
  simp [EV,evalHOLExact,hp] at e1; subst e1
  obtain ⟨y2,rfl⟩ := he2 _ e2'
  obtain ⟨y3,rfl⟩ := he3 _ e3'
  have e := callee_eq inst lookup
  exact ⟨by rw [e]; simp [h2,h3],⟨y2,by rw [e]; simp [h23]⟩,y3,by rw [e]; simp⟩

end hl

/-- The heap pointer is at or above `H0`. -/
def HGe (H0 : BitVec 64) (G : GA) : Prop := ∃ H1 : BitVec 64, HeapIs G H1 ∧ H0.toNat ≤ H1.toNat

section cs2
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat} {GI : GA → Prop}

theorem cs_to (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "to") = some (.val (.word Y))) ∧ GI G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ GI G) (sourceFunctionBody Guest.guestFn_tx_put_to) :=
  aqgd_conseq (aqgd_keepGI (GI := GI) (keepsGA_of_installed originalRuntimeCode_txPutTo_lookup (by decide))
      (putTo_win hF hDF Lo hLo8 hw P h1 (by omega)))
    (fun _ _ _ ⟨⟨hd,_⟩,g⟩ => ⟨hd,g⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

theorem cs_al (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "dst") = some (.val (.word P)) ∧
        (∃ Y : BitVec 64, L.lookup (ofString "recs") = some (.val (.word Y))) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y))) ∧ GI G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ GI G) (sourceFunctionBody Guest.guestFn_tx_put_access_list) :=
  aqgd_conseq (aqgd_keepGI (GI := GI) (keepsGA_of_installed originalRuntimeCode_txPutAccessList_lookup (by decide))
      (putAccessList_win hF hDF Lo hLo8 hw P h1 h2))
    (fun _ _ _ ⟨⟨hd,_⟩,g⟩ => ⟨hd,g⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

theorem cs_bh (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "dst") = some (.val (.word P)) ∧
        (∃ Y : BitVec 64, L.lookup (ofString "buf") = some (.val (.word Y))) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y))) ∧ GI G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ GI G) (sourceFunctionBody Guest.guestFn_tx_put_blob_hashes) :=
  aqgd_conseq (aqgd_keepGI (GI := GI) (keepsGA_of_installed originalRuntimeCode_txPutBlobHashes_lookup (by decide))
      (aqgd_exE (fun Bf => aqgd_exE (fun Nn => putBlobHashes_win hF hDF Lo hLo8 hw P Bf Nn h1 h2))))
    (fun _ _ _ ⟨⟨hd,⟨Bf,hb⟩,⟨Nn,hn⟩⟩,g⟩ => ⟨⟨Bf,Nn,hd,hb,hn⟩,g⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

#print axioms cs_bh
end cs2

section cs3
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- `tx_put_u256` as a cursor writer keeping "heap pointer at or above `H0`". -/
theorem cs_u256E (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo : BitVec 64)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (H0 : BitVec 64) (hLoH : Lo.toNat ≤ H0.toNat)
    (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "dst") = some (.val (.word P)) ∧ HGe H0 G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ HGe H0 G) (sourceFunctionBody Guest.guestFn_tx_put_u256) :=
  aqgd_conseq (P := fun L M G => ∃ H1 : BitVec 64, (L.lookup (ofString "dst") = some (.val (.word P)) ∧
      HeapIs G H1) ∧ H0.toNat ≤ H1.toNat) (Q := fun _ _ _ => True)
    (aqgd_exE (fun H1 => fun F s code dom aw sl H hH ⟨pre,le⟩ => by
      obtain ⟨m,a,n,r,c,b⟩ := cs_u256 (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C)
        (SKB := SKB) (Nj := Nj) hF hDF hcap Lo hLo8 hw H1 (by omega) P h1 h2 F s code dom aw sl H hH pre
      exact ⟨m,a,fun e => let ⟨sl',H',hH',_⟩ := n e; ⟨sl',H',hH',trivial⟩,
        fun v e => let ⟨H',hH',rr,hh⟩ := r v e; ⟨H',hH',rr,H1,hh,le⟩,c,b⟩))
    (fun _ _ _ ⟨hd,H1,hh,le⟩ => ⟨H1,⟨hd,hh⟩,le⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

/-- `tx_put_authorizations` as a cursor writer keeping "heap pointer at or above `H0`". -/
theorem cs_auE (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo : BitVec 64)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (H0 : BitVec 64) (hLoH : Lo.toNat ≤ H0.toNat)
    (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "dst") = some (.val (.word P)) ∧ HGe H0 G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ HGe H0 G) (sourceFunctionBody Guest.guestFn_tx_put_authorizations) :=
  aqgd_conseq (P := fun L M G => ∃ H1 : BitVec 64, (L.lookup (ofString "dst") = some (.val (.word P)) ∧
      HeapIs G H1) ∧ H0.toNat ≤ H1.toNat) (Q := fun _ _ _ => True)
    (aqgd_exE (fun H1 => fun F s code dom aw sl H hH ⟨pre,le⟩ => by
      obtain ⟨m,a,n,r,c,b⟩ := putAuthorizations_win (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J)
        (C := C) (SKB := SKB) (Nj := Nj) hF hDF hcap Lo hLo8 hw P H1 h1 h2 (by omega) F s code dom aw sl H hH pre
      exact ⟨m,a,fun e => let ⟨sl',H',hH',_⟩ := n e; ⟨sl',H',hH',trivial⟩,
        fun v e => let ⟨H',hH',rr,hh⟩ := r v e; ⟨H',hH',rr,H1,hh,le⟩,c,b⟩))
    (fun _ _ _ ⟨hd,H1,hh,le⟩ => ⟨H1,⟨hd,hh⟩,le⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

#print axioms cs_auE
end cs3
end InitECandidate.Runtime
