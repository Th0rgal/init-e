import InitECandidate.Runtime.EncCursorGD
/-!
Adapters of the fenced writer specs to the cursor step (pass-through globals invariant for globals-keeping writers),
callee-entry lemmas for writer calls `f(p, …)`, and the locals-only cursor step.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evalList_cons' {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (es : List (ExpHOL 64))
    (vs : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (e :: es) = some vs) :
    ∃ v vs', vs = v :: vs' ∧ EV s e = some v ∧
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) es = some vs' := by
  rw [evalListHOLFinite_eq_toExact] at h ⊢
  simp only [evalListHOLExact] at h
  split at h
  · rename_i v vs' h1 h2
    simp only [Option.some.injEq] at h
    exact ⟨v,vs',h.symm,h1,h2⟩
  · cases h

theorem evalList_nil' {F : Type} (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some vs) : vs = [] := by
  rw [evalListHOLFinite_eq_toExact] at h
  simp [evalListHOLExact] at h; exact h

section gi
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A globals-keeping body keeps any globals invariant. -/
theorem aqgd_keepGI {GI : GA → Prop} {P Q : GA → Mem → GA → Prop} {body : ProgHOL 64}
    (hk : keepsGA goodGA body = true) (h : AQGD D B A w Vn P Q RR body) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ GI G) (fun L M G => Q L M G ∧ GI G)
      (fun v M G => RR v M G ∧ GI G) body := by
  intro F s code dom aw sl H hH ⟨pre,g⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  have glob := evaluate_keepsGA goodGA goodGA_bodies body hk s code
  unfold GIs at hH; subst hH
  refine ⟨m,a,fun e => ?_,fun v e => ?_,c,b⟩
  · obtain ⟨sl',H',hH',q⟩ := n e
    unfold GIs at hH'
    exact ⟨sl',H',hH',q,by rw [← hH',glob]; exact g⟩
  · obtain ⟨H',hH',rr⟩ := r v e
    unfold GIs at hH'
    exact ⟨H',hH',rr,by rw [← hH',glob]; exact g⟩

#print axioms aqgd_keepGI
end gi
/-- Callee entry of a two-parameter writer called as `f(p, e2)` with `e2` word-valued. -/
theorem hpe2 {f q : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(ofString "dst",.one),(q,.one)],bd,rs0)) (hq : ofString "dst" ≠ q)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (e2 : ExpHOL 64) (P : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (he2 : ∀ v, EV s e2 = some v → ∃ y : BitVec 64, v = .val (.word y)) {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),e2] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    callee.lookup (ofString "dst") = some (.val (.word P)) ∧ ∃ Y : BitVec 64, callee.lookup q = some (.val (.word Y)) := by
  obtain ⟨v1,vs,rfl,e1,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,e2',r2⟩ := evalList_cons' s _ _ _ r1
  have := evalList_nil' s _ r2; subst this
  simp [EV,evalHOLExact,hp] at e1; subst e1
  obtain ⟨y,rfl⟩ := he2 _ e2'
  have e := callee_eq inst lookup
  exact ⟨by rw [e]; simp [hq],y,by rw [e]; simp⟩

/-- Callee entry of `rlp_encode_bytes(p, e2, e3)` with `e3` word-valued. -/
theorem hpe3 {F : Type} (s : PanSemStateFiniteExact 64 F) (e2 e3 : ExpHOL 64) (P : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (he3 : ∀ v, EV s e3 = some v → ∃ y : BitVec 64, v = .val (.word y)) {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : GA} {rs : ShapeHOL}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),e2,e3] = some values)
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_encode_bytes") values = some (body,callee,rs)) :
    callee.lookup (ofString "dst") = some (.val (.word P)) ∧
      ∃ Y : BitVec 64, callee.lookup (ofString "n") = some (.val (.word Y)) := by
  obtain ⟨v1,vs,rfl,e1,r1⟩ := evalList_cons' s _ _ _ args
  obtain ⟨v2,vs2,rfl,_,r2⟩ := evalList_cons' s _ _ _ r1
  obtain ⟨v3,vs3,rfl,e3',r3⟩ := evalList_cons' s _ _ _ r2
  have := evalList_nil' s _ r3; subst this
  simp [EV,evalHOLExact,hp] at e1; subst e1
  obtain ⟨y,rfl⟩ := he3 _ e3'
  have e := callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
  exact ⟨by rw [e]; simp (config := {decide := true}),y,by rw [e]; simp⟩

section ad
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat} {GI : GA → Prop}

theorem cs_bytes (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "n") = some (.val (.word Y))) ∧ GI G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ GI G) (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) :=
  aqgd_conseq (aqgd_keepGI (GI := GI) (keepsGA_of_installed originalRuntimeCode_rlpEncodeBytes_lookup (by decide))
      (aqgd_exE (fun N => encodeBytes_win hF hDF Lo hLo8 hw P N h1 (by omega))))
    (fun _ _ _ ⟨⟨hd,N,hn⟩,g⟩ => ⟨⟨N,hd,hn⟩,g⟩) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)

theorem cs_word (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "w") = some (.val (.word Y))) ∧ GI G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ GI G) (sourceFunctionBody Guest.guestFn_rlp_encode_word) :=
  aqgd_conseq (aqgd_keepGI (GI := GI) (keepsGA_of_installed originalRuntimeCode_rlpEncodeWord_lookup (by decide))
      (aqgd_exE (fun N => encodeWord_win hF Lo hLo8 hw P N h1 (by omega))))
    (fun _ _ _ ⟨⟨hd,N,hn⟩,g⟩ => ⟨⟨N,hd,hn⟩,g⟩) (fun _ _ _ _ => trivial) (fun _ _ _ ⟨h,g⟩ => ⟨wret_of_hdr h,g⟩)

theorem cs_lh (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (P : BitVec 64) (h1 : Lo.toNat ≤ P.toNat) (h2 : P.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False)
      (fun L _ G => (L.lookup (ofString "dst") = some (.val (.word P)) ∧
        ∃ Y : BitVec 64, L.lookup (ofString "payload_len") = some (.val (.word Y))) ∧ GI G) (fun _ _ _ => True)
      (fun r _ G => WRet DF P r ∧ GI G) (sourceFunctionBody Guest.guestFn_rlp_encode_list_header) :=
  aqgd_conseq (aqgd_keepGI (GI := GI) (keepsGA_of_installed originalRuntimeCode_rlpEncodeListHeader_lookup (by decide))
      (aqgd_exE (fun N => listHeader_win hF Lo hLo8 hw P N h1 (by omega))))
    (fun _ _ _ ⟨⟨hd,N,hn⟩,g⟩ => ⟨⟨N,hd,hn⟩,g⟩) (fun _ _ _ _ => trivial) (fun _ _ _ ⟨h,g⟩ => ⟨wret_of_hdr h,g⟩)

#print axioms cs_bytes
#print axioms cs_word
#print axioms cs_lh
end ad
/-- Locals-only cursor state. -/
def CIL (DF : Nat) (base : GA → Prop) (Dst : BitVec 64) (L : GA) : Prop :=
  base L ∧ ∃ P : BitVec 64, L.lookup (ofString "p") = some (.val (.word P)) ∧ Dst.toNat ≤ P.toNat ∧ P.toNat ≤ DF + 8

section csl
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {DF : Nat}

theorem cursor_stepL (hDF : DF ≤ 2 ^ 62) {base : GA → Prop} (Dst : BitVec 64)
    (hbw : ∀ L v, base L → base (L.update (ofString "w",v))) (hbp : ∀ L v, base L → base (L.update (ofString "p",v)))
    (function : MlS) (arguments : List (ExpHOL 64)) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (rs : ShapeHOL) (installed : originalRuntimeCode.lookup function = some (parameters,body,rs))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (Pe' : BitVec 64 → GA → Prop)
    (hspec : ∀ P : BitVec 64, Dst.toNat ≤ P.toNat → P.toNat ≤ DF + 8 →
      AQGD D B A w (fun _ => False) (fun L _ G => Pe' P L ∧ (fun _ => True) G) (fun _ _ _ => True)
        (fun r _ G => WRet DF P r ∧ (fun _ => True) G) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs' (P : BitVec 64), base s.locals →
      s.locals.lookup (ofString "p") = some (.val (.word P)) →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs') → Pe' P callee) :
    AQGD D B A w (fun _ => False) (fun L _ _ => CIL DF base Dst L) (fun L _ _ => CIL DF base Dst L) RR
      (.seq (.call (some (some (.local,ofString "w"),none)) function arguments)
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]))) :=
  aqgd_conseq (cursor_step (GI := fun _ => True) hDF Dst hbw hbp function arguments parameters body rs installed allOne
      Pe' hspec hpe)
    (fun _ _ _ ⟨b,c⟩ => ⟨b,trivial,c⟩) (fun _ _ _ ⟨b,_,c⟩ => ⟨b,c⟩) (fun _ _ _ h => h)

#print axioms cursor_stepL
end csl

def alBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "pl") ShapeHOL.one (ofString "access_list_payload_len") [ExpHOL.var VarKind.local (ofString "recs"), ExpHOL.var VarKind.local (ofString "n")] (ProgHOL.decCall (ofString "w") ShapeHOL.one (ofString "rlp_encode_list_header") [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "pl")] (ProgHOL.dec (ofString "p") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "w")]) (ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) (ProgHOL.dec (ofString "rec") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "recs"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 24#64]]) (ProgHOL.dec (ofString "ns") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "rec"), ExpHOL.const 16#64])) (ProgHOL.dec (ofString "inner") ShapeHOL.one (ExpHOL.panop PanOp.mul [ExpHOL.const 33#64, ExpHOL.var VarKind.local (ofString "ns")]) (ProgHOL.decCall (ofString "ih") ShapeHOL.one (ofString "rlp_list_header_len") [ExpHOL.var VarKind.local (ofString "inner")] (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.op BinOp.add [ExpHOL.const 21#64, ExpHOL.var VarKind.local (ofString "ih"), ExpHOL.var VarKind.local (ofString "inner")]]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "rec"), ExpHOL.const 0#64]), ExpHOL.const 20#64]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_list_header") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "inner")]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.dec (ofString "keys") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "rec"), ExpHOL.const 8#64])) (ProgHOL.dec (ofString "j") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "j")) (ExpHOL.var VarKind.local (ofString "ns"))) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "keys"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 32#64]], ExpHOL.const 32#64]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "p") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "w")])) (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 1#64]))))) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))))))))))))))) (ProgHOL.return (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "dst")]))))))

theorem alBody_eq : sourceFunctionBody Guest.guestFn_tx_put_access_list = alBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_tx_put_access_list,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
end InitECandidate.Runtime
