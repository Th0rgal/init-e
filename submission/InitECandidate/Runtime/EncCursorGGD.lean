import InitECandidate.Runtime.EncAccessListGD
/-!
The pinned-journal arena `JWSN`, `tx_put_u256` as a cursor writer keeping the heap pointer, and globals-aware cursor
rules (`CIG`: cursor state with a globals invariant).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The journal arena with the journal counter pinned to `Nj`. -/
def JWSN (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Nj : BitVec 64) (g : GA) : Prop :=
  JWS SP0 P0 FM G0 J C SKB g ∧ g.lookup (ofString "journal_n") = some (.val (.word Nj))

section pa
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A precondition conjunct implied by the arena may be dropped. -/
theorem aqgd_preA {X : GA → Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} (hA : ∀ g, A g → X g)
    (h : AQGD D B A w Vn (fun L M G => P L M G ∧ X G) Q RR p) : AQGD D B A w Vn P Q RR p := by
  intro F s code dom aw sl H hH pre
  have := hH; unfold GIs at this; subst this
  exact h F s code dom aw sl _ rfl ⟨pre,hA _ aw⟩

#print axioms aqgd_preA
end pa

section cu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- `tx_put_u256` as a cursor writer over the pinned-journal arena, keeping the heap pointer `H`. -/
theorem cs_u256 (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (Lo : BitVec 64)
    (hLo8 : Lo.toNat % 8 = 0) (hw : w.toNat < Lo.toNat) (H : BitVec 64) (hLoH : Lo.toNat ≤ H.toNat)
    (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L _ G => L.lookup (ofString "dst") = some (.val (.word P)) ∧ HeapIs G H) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ HeapIs G H) (sourceFunctionBody Guest.guestFn_tx_put_u256) := by
  have h := putU256_win (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB) (B := B)
    hF hDF hcap Lo hLo8 hw P H Nj h1 (by omega) hLoH
  have h' := aqgd_strengthen (X := fun g => g.lookup (ofString "journal_n") = some (.val (.word Nj))) h
    (fun s code x => (evaluate_keeps_journal_n _
      (keepsJournalN_of_installed originalRuntimeCode_txPutU256_lookup (by decide)) s code).trans x)
  refine aqgd_preA (X := fun g => g.lookup (ofString "journal_n") = some (.val (.word Nj))) (fun _ h => h.2) ?_
  exact aqgd_conseq h' (fun _ _ _ ⟨⟨hd,hH⟩,hn⟩ => ⟨hd,hH,hn⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

#print axioms cs_u256
end cu
/-- Cursor state with a globals invariant. -/
def CIG (DF : Nat) (base GI : GA → Prop) (Dst : BitVec 64) (L G : GA) : Prop :=
  base L ∧ GI G ∧ ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧ Dst.toNat ≤ P.toNat ∧
    P.toNat ≤ DF + 8

def CIGW (DF : Nat) (base GI : GA → Prop) (Dst : BitVec 64) (L G : GA) : Prop :=
  base L ∧ GI G ∧ ∃ P R : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧
    L.lookup (ofString "w") = some (.val (.word R)) ∧ Dst.toNat ≤ P.toNat ∧ P.toNat + R.toNat ≤ DF + 8

section cg
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {DF : Nat} {base GI : GA → Prop}

theorem csg_call (Dst : BitVec 64) (hbw : ∀ L v, base L → base (L.update (ofString "w",v)))
    (function : MlS) (arguments : List (ExpHOL 64)) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (rs : ShapeHOL) (installed : originalRuntimeCode.lookup function = some (parameters,body,rs))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (Pe' : BitVec 64 → GA → Prop)
    (hspec : ∀ P : BitVec 64, Dst.toNat ≤ P.toNat → P.toNat ≤ DF + 8 →
      AQGD D B A w (fun _ => False) (fun L _ G => Pe' P L ∧ GI G) (fun _ _ _ => True)
        (fun r _ G => WRet DF P r ∧ GI G) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs' (P : BitVec 64), base s.locals →
      s.locals.lookup (ofString "p") = some (.val (.word P)) →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs') → Pe' P callee) :
    AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base GI Dst L G) (fun L _ G => CIGW DF base GI Dst L G) RR
      (.call (some (some (.local,ofString "w"),none)) function arguments) :=
  aqgd_callAssignF (Vn' := fun _ => False)
    (Pe := fun (L0 : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (G : GA) => Pe' (wordOf L0 (ofString "p")) L ∧ GI G)
    (RRe := fun (L0 : GA) (_ : Mem) (_ : GA) (r : ValueHOL 64) (_ : Mem) (G' : GA) =>
      WRet DF (wordOf L0 (ofString "p")) r ∧ GI G')
    _ _ _ _ _ _ installed allOne (fun h => h)
    (fun L0 _ _ ⟨_,_,P,hp,h1,h2⟩ => by rw [wordOf_eq hp]; exact hspec P h1 h2)
    (fun s values callee rs' _ H hH ⟨hb,hg,P,hp,_⟩ _ args lookup => by
      unfold GIs at hH; subst hH
      rw [wordOf_eq hp]; exact ⟨hpe s values callee rs' P hb hp args lookup,hg⟩)
    (fun L _ _ v _ _ ⟨hb,_,P,hp,h1,_⟩ ⟨⟨R,hr,hR⟩,hg⟩ => by
      rw [wordOf_eq hp] at hR
      subst hr
      exact ⟨hbw _ _ hb,hg,P,R,by rw [lookup_update_ne' _ _ (by decide)]; exact hp,lookup_update_eq' _ _ _,h1,hR⟩)

theorem csg_adv (hDF : DF ≤ 2 ^ 62) (Dst : BitVec 64) (hbp : ∀ L v, base L → base (L.update (ofString "p",v))) :
    AQGD D B A w (fun _ => False) (fun L _ G => CIGW DF base GI Dst L G) (fun L _ G => CIG DF base GI Dst L G) RR
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"),.var .local (ofString "w")])) :=
  aqgd_assignLocal _ _ (fun s v _ _ ⟨hb,hg,P,R,hp,hr,h1,h2⟩ _ ev => by
    simp [EV,evalHOLExact,evalListHOLExact,hp,hr,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
    have e1 : (P + R).toNat = P.toNat + R.toNat := by simp [BitVec.toNat_add]; omega
    exact ⟨hbp _ _ hb,hg,_,lookup_update_eq' _ _ _,by omega,by omega⟩)

theorem cig_dec {base' : GA → Prop} (Dst : BitVec 64) (name : MlS) (init : ExpHOL 64) {body : ProgHOL 64}
    (hbu : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, base s.locals → EV s init = some v →
      base' (s.locals.update (name,v)))
    (hbr : ∀ L L' : GA, base L → base' L' → base (L'.resVarEq (name,L.lookup name)))
    (hp : ofString "p" ≠ name)
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base' GI Dst L G) (fun L _ G => CIG DF base' GI Dst L G) RR body) :
    AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base GI Dst L G) (fun L _ G => CIG DF base GI Dst L G) RR
      (.dec name .one init body) :=
  aqgd_dec _ _ _ (fun h => h.elim)
    (fun s v _ _ hG ⟨b,g,P,hP,h1,h2⟩ _ ev _ => by
      unfold GIs at hG; subst hG
      exact ⟨hbu s v b ev,g,P,by rw [lookup_update_ne' _ _ hp]; exact hP,h1,h2⟩) hb
    (fun L _ _ L' _ _ ⟨b,_⟩ ⟨b',g,P,hP,h1,h2⟩ => ⟨hbr L L' b b',g,P,by rw [resVarEq_lookup_ne' _ _ _ _ hp]; exact hP,h1,h2⟩)

theorem cig_decCall_mf {base' : GA → Prop} (Dst : BitVec 64) (name function : MlS) (arguments : List (ExpHOL 64))
    {cont : ProgHOL 64} (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (hbu : ∀ L v, base L → shapeEqHOL (shapeOfHOLExact v) .one = true → base' (L.update (name,v)))
    (hbr : ∀ L L' : GA, base L → base' L' → base (L'.resVarEq (name,L.lookup name)))
    (hp : ofString "p" ≠ name)
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base' GI Dst L G) (fun L _ G => CIG DF base' GI Dst L G) RR cont) :
    AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base GI Dst L G) (fun L _ G => CIG DF base GI Dst L G) RR
      (.decCall name .one function arguments cont) :=
  aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    (Pc := fun L _ G => CIG DF base' GI Dst L G) (Qc := fun L _ G => CIG DF base' GI Dst L G) _ _ _ _ _ _ _ installed
    (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim)
    (fun L M G v M' G' ⟨b,g,P,hP,h1,h2⟩ ⟨_,e2⟩ ok => by
      subst e2
      exact ⟨hbu L v b ok,g,P,by rw [lookup_update_ne' _ _ hp]; exact hP,h1,h2⟩) hb
    (fun L _ _ L' _ _ ⟨b,_⟩ ⟨b',g,P,hP,h1,h2⟩ => ⟨hbr L L' b b',g,P,by rw [resVarEq_lookup_ne' _ _ _ _ hp]; exact hP,h1,h2⟩)

theorem cig_assign (Dst : BitVec 64) (x : MlS) (e : ExpHOL 64) (hbu : ∀ L v, base L → base (L.update (x,v)))
    (hp : ofString "p" ≠ x) :
    AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base GI Dst L G) (fun L _ G => CIG DF base GI Dst L G) RR
      (.assign .local x e) :=
  aqgd_assignLocal _ _ (fun s v _ _ ⟨b,g,P,hP,h1,h2⟩ _ _ =>
    ⟨hbu _ v b,g,P,by rw [lookup_update_ne' _ _ hp]; exact hP,h1,h2⟩)

theorem cig_while (Dst : BitVec 64) (c : ExpHOL 64) {body : ProgHOL 64}
    (hb : AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base GI Dst L G) (fun L _ G => CIG DF base GI Dst L G) RR body) :
    AQGD D B A w (fun _ => False) (fun L _ G => CIG DF base GI Dst L G) (fun L _ G => CIG DF base GI Dst L G) RR
      (.while c body) :=
  aqgd_conseq (aqgd_whileBreak (I := fun L _ G => CIG DF base GI Dst L G) (C := fun _ _ _ => True)
      (Qb := fun _ _ _ => False) _ (fun _ _ _ _ _ _ _ _ => trivial)
      (aqgb_of_aqgd (aqgd_conseq hb (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)

#print axioms csg_call
#print axioms cig_decCall_mf
end cg
/-- Callee entry of `tx_put_u256(p, e2)`: `dst` bound to the cursor. -/
theorem hpeU {F : Type} (s : PanSemStateFiniteExact 64 F) (e2 : ExpHOL 64) (P : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P))) {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "tx_put_u256") values = some (body,callee,rs)) :
    callee.lookup (ofString "dst") = some (.val (.word P)) := by
  obtain ⟨v1,vs,rfl,e1,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  simp [EV,evalHOLExact,hp] at e1; subst e1
  have e := callee_eq originalRuntimeCode_txPutU256_lookup lookup
  rw [e]; simp (config := {decide := true})

def auBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "total") ShapeHOL.one (ofString "auth_list_payload_len") [ExpHOL.var VarKind.local (ofString "recs"), ExpHOL.var VarKind.local (ofString "n")] (ProgHOL.decCall (ofString "w") ShapeHOL.one (ofString "rlp_encode_list_header") [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "total")] (ProgHOL.dec (ofString "p") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "w")]) (ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.dec (ofString "a") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "recs"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 120#64]]) (ProgHOL.decCall (ofString "pl") ShapeHOL.one (ofString "auth_payload_len") [ExpHOL.var VarKind.local (ofString "a")] (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "pl")]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.const 0#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.const 32#64]), ExpHOL.const 20#64]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.const 40#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.const 48#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.const 56#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.const 88#64])]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64]))))))))))))))))))) (ProgHOL.return (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "dst")]))))))

theorem auBody_eq : sourceFunctionBody Guest.guestFn_tx_put_authorizations = auBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_tx_put_authorizations,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
end InitECandidate.Runtime
