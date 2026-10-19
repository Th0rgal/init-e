import InitECandidate.Runtime.DigitsDivmodGD
import InitECandidate.Runtime.OriginalUdivmodCode
/-!
Window frames of the actual `u256_divmod` and `u256_div`: every store lands in the 640-byte `u256_ws` workspace.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Callee entry of a function with parameters (one, one, four words): only the four-word one is not a word. -/
theorem callee_114_sl {f p q r : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.one),(q,.one),(r,.comb [.one,.one,.one,.one])],bd,rs0))
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    SL (fun x => x ≠ r) callee := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b0 cl rs1 found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hc,_⟩ := h
    have hl : callee.lookup = cl := by rw [← hc]
    clear hc
    unfold Flapjack.lookupCodeHOLExact at found
    rw [inst] at found
    dsimp only at found
    split at found
    · rename_i cond
      obtain ⟨_,hlen,hall⟩ := cond
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨_,hcl,_⟩ := found
      match values, hlen, hall with
      | [v0,v1,v2], _, hall =>
        simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,
          Bool.and_eq_true] at hall
        obtain ⟨s0,s1,_⟩ := hall
        obtain ⟨a,rfl⟩ : ∃ a : BitVec 64, v0 = .val (.word a) := scalar_of_shape s0
        obtain ⟨b,rfl⟩ : ∃ b : BitVec 64, v1 = .val (.word b) := scalar_of_shape s1
        subst hcl
        intro x hx v hv
        rw [hl] at hv
        simp only [List.map_cons,List.map_nil,List.zip_cons_cons,List.zip_nil_right,List.foldl_cons,
          List.foldl_nil] at hv
        by_cases e2 : x = r
        · exact absurd e2 hx
        · rw [if_neg e2] at hv
          by_cases e1 : x = q
          · rw [if_pos e1] at hv; simp at hv; exact ⟨b,hv.symm⟩
          · rw [if_neg e1] at hv
            by_cases e0 : x = p
            · rw [if_pos e0] at hv; simp at hv; exact ⟨a,hv.symm⟩
            · rw [if_neg e0] at hv; cases hv
    · cases found

#print axioms callee_114_sl

def udmBody : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.or [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "b"))]) (ExpHOL.const 0#64)) (ProgHOL.return (ExpHOL.rstruct [ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64])) ProgHOL.skip) (ProgHOL.decCall (ofString "lt") ShapeHOL.one (ofString "u256_lt") [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.var VarKind.local (ofString "b")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "lt")) (ExpHOL.const 1#64)) (ProgHOL.return (ExpHOL.rstruct [ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "a"))])) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.or [ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "b"))]) (ExpHOL.const 0#64)) (ProgHOL.decCall (ofString "qr") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]) (ofString "udivmod") [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "b"))] (ProgHOL.return (ExpHOL.rstruct [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64]))) ProgHOL.skip) (ProgHOL.dec (ofString "u") ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const 424#64]) (ProgHOL.seq (ProgHOL.call (some (none, none)) (ofString "u256_to_digits") [ExpHOL.var VarKind.local (ofString "u"), ExpHOL.var VarKind.local (ofString "a")]) (ProgHOL.decCall (ofString "r") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "digits_divmod") [ExpHOL.var VarKind.local (ofString "u"), ExpHOL.const 8#64, ExpHOL.var VarKind.local (ofString "b")] (ProgHOL.decCall (ofString "q") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "digits_to_u256") [ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "u256_ws"), ExpHOL.const 216#64]] (ProgHOL.return (ExpHOL.rstruct [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "q")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "q")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "q")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "q")), ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "r")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "r")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "r")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "r"))])))))))))

theorem udmBody_eq : sourceFunctionBody Guest.guestFn_u256_divmod = udmBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_u256_divmod,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Fixed locals of `u256_divmod(a, b)`. -/
def udmL (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : List (MlS × ValueHOL 64) :=
  [(ofString "a",.rStruct [.val (.word a0),.val (.word a1),.val (.word a2),.val (.word a3)]),
    (ofString "b",.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)])]

section udm
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {U : BitVec 64}

theorem u256Divmod_window_fixed (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    AQGD D B A w (fun _ => False) (fun L _ _ => FixL (udmL a0 a1 a2 a3 b0 b1 b2 b3) L) (fun _ _ _ => False)
      (fun _ _ _ => True) udmBody := by
  unfold udmBody
  let BNZ : Prop := ¬ (b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0)
  have hb := fun {F : Type} (s : PanSemStateFiniteExact 64 F) (lp : FixL (udmL a0 a1 a2 a3 b0 b1 b2 b3) s.locals) =>
    fixL_get lp (ofString "b") (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)]) (by simp [udmL])
  -- b = 0: early return
  refine aqgd_seq (Q := fun L _ _ => FixL (udmL a0 a1 a2 a3 b0 b1 b2 b3) L ∧ BNZ)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => BNZ) _ ?_
      (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · intro F s x _ _ _ lp _ ev
    refine ⟨fun _ => trivial,fun z hz => ?_⟩
    obtain ⟨e0,e1,e2,e3⟩ := hz
    simp [EV,evalHOLExact,evalListHOLExact,hb s lp,e0,e1,e2,e3,wordOpHOL,wordOp,valueIsWord,valueWord,
      Compiler.Encoders.Asm.wordCmpHOL] at ev
    subst z; exact absurd ev (by decide)
  let S := fun L => FixL (udmL a0 a1 a2 a3 b0 b1 b2 b3) L ∧ BNZ
  refine r_decCall (LB := S) (LQ' := fun _ => False) _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup
    (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) (fun h => h.elim)
    (fun L v ⟨lp,bz⟩ _ => ⟨fixL_upd lp _ _ (by simp only [udmL,List.map_cons,List.map_nil]; decide),bz⟩) ?_
    (fun _ _ _ h => h)
  refine aqgd_seq (r_ite _ (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)) aqgd_skip) ?_
  refine aqgd_seq (r_ite _ (r_decCall (LB := S) (LQ' := fun _ => False) _ _ _ _ _ _ _ originalRuntimeCode_udivmod_lookup
    (memoryFrame_of_good originalRuntimeCode_udivmod_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_udivmod) (by body_check Guest.guestFn_udivmod) (fun h => h.elim)
    (fun L v ⟨lp,bz⟩ _ => ⟨fixL_upd lp _ _ (by simp only [udmL,List.map_cons,List.map_nil]; decide),bz⟩)
    (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)) (fun _ _ _ h => h.elim)) aqgd_skip) ?_
  -- u = u256_ws + 424; u256_to_digits(u, a)
  let S2 := fun L => FixL ((ofString "u",.val (.word (U + 424#64))) :: udmL a0 a1 a2 a3 b0 b1 b2 b3) L ∧ BNZ
  refine r_dec (LB := S2) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) (fun s v aw ⟨lp,bz⟩ ev => by
      have hg := hA _ aw
      unfold WsG at hg
      simp [EV,evalHOLExact,evalListHOLExact,hg,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
      exact ⟨fixL_cons lp _ _ (by simp only [udmL,List.map_cons,List.map_nil]; decide),bz⟩) ?_ (fun _ _ _ h => h)
  have hwk : ∀ k, k < 8 → w ≠ U + 424#64 + BitVec.ofNat 64 (8 * k) := by
    intro k hk e; apply hw; subst e; unfold WS; simp [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
  refine aqgd_seq (Q := fun L _ _ => S2 L)
    (aqgd_callSpecS (Vn' := fun _ => False)
      (Pe := fun (_ : GA) (M0' : Mem) (_ : GA) (L : GA) (M : Mem) (_ : GA) => LPA (U + 424#64) a0 a1 a2 a3 L ∧ M = M0')
      (RRe := fun (_ : GA) (M0' : Mem) (_ : GA) (_ : ValueHOL 64) (M' : Mem) (_ : GA) =>
        U2D (U + 424#64) a0 a1 a2 a3 M0' 8 M')
      _ _ _ _ _ vmLookup_u256_to_digits (fun _ _ _ _ _ h => h.elim)
      (fun _ M0' _ _ => by
        rw [u2dBody_eq]
        exact aqgd_conseq (u2d_spec (M0 := M0') hwk) (fun _ _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ _ h => h))
      ?_ (fun _ _ _ _ _ _ pre _ => pre)) ?_
  · intro F s values callee rs _ _ _ ⟨lp,_⟩ _ args lookup
    have hu := fixL_get lp (ofString "u") (.val (.word (U + 424#64))) (by simp [udmL])
    have ha := fixL_get lp (ofString "a")
      (.rStruct [.val (.word a0),.val (.word a1),.val (.word a2),.val (.word a3)]) (by simp [udmL])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hu,ha] at args
    subst args
    refine ⟨?_,rfl⟩
    have e := callee_eq vmLookup_u256_to_digits lookup
    unfold LPA; rw [e]; simp; decide
  -- r = digits_divmod(u, 8, b)
  refine aqgd_decCallSpecS (Vn' := fun x => x ≠ ofString "d")
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) =>
      FixL [(ofString "u",.val (.word (U + 424#64))),(ofString "m",.val (.word 8#64)),
        (ofString "d",.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)])] L)
    (RRe := fun _ _ _ _ _ _ => True) (Pc := fun L _ _ => S2 L) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_digitsDivmod_lookup
    (fun _ _ _ h => callee_114_sl originalRuntimeCode_digitsDivmod_lookup h)
    (fun _ _ _ ⟨_,bz⟩ => aqgd_conseq (digitsDivmod_window' hA hU hw (by decide) bz) (fun _ _ _ h => h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)) ?_ (fun h => h.elim)
    (fun L _ _ v _ _ ⟨lp,bz⟩ _ _ => ⟨fixL_upd lp _ _ (by simp only [udmL,List.map_cons,List.map_nil]; decide),bz⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  · intro F s values callee rs _ _ _ ⟨lp,_⟩ _ args lookup
    have hu := fixL_get lp (ofString "u") (.val (.word (U + 424#64))) (by simp [udmL])
    have hb' := fixL_get lp (ofString "b")
      (.rStruct [.val (.word b0),.val (.word b1),.val (.word b2),.val (.word b3)]) (by simp [udmL])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hu,hb'] at args
    subst args
    have e := callee_eq originalRuntimeCode_digitsDivmod_lookup lookup
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  -- q = digits_to_u256(u256_ws + 216); return
  exact r_decCall (LB := S2) (LQ' := fun _ => False) _ _ _ _ _ _ _ vmLookup_digits_to_u256
    (memoryFrame_of_good vmLookup_digits_to_u256 (by decide) (by decide))
    (by body_check Guest.guestFn_digits_to_u256) (by body_check Guest.guestFn_digits_to_u256) (fun h => h.elim)
    (fun L v ⟨lp,bz⟩ _ => ⟨fixL_upd lp _ _ (by simp only [udmL,List.map_cons,List.map_nil]; decide),bz⟩)
    (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)) (fun _ _ _ h => h)

#print axioms u256Divmod_window_fixed

/-- Window frame of the actual `u256_divmod(a, b)` on four-word arguments. -/
theorem u256Divmod_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w) :
    AQGD D B A w (fun _ => False) (fun L _ _ => U4 (ofString "a") L ∧ U4 (ofString "b") L) (fun _ _ _ => False)
      (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_u256_divmod) := by
  rw [udmBody_eq]
  refine aqgd_conseq (P := fun L _ _ => ∃ x : (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) ×
      (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64),
      FixL (udmL x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) L)
    (aqgd_exE (fun x => u256Divmod_window_fixed hA hU hw _ _ _ _ _ _ _ _)) ?_ (fun _ _ _ h => h) (fun _ _ _ h => h)
  intro L _ _ ⟨⟨a0,a1,a2,a3,ha⟩,⟨b0,b1,b2,b3,hb⟩⟩
  refine ⟨((a0,a1,a2,a3),(b0,b1,b2,b3)),fun p hp => ?_⟩
  simp only [udmL,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact ha
  · exact hb

#print axioms u256Divmod_window

def udBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "qr") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_divmod") [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.var VarKind.local (ofString "b")] (ProgHOL.return (ExpHOL.rstruct [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "qr"))]))

theorem udBody_eq : sourceFunctionBody Guest.guestFn_u256_div = udBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_u256_div,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

/-- Window frame of the actual `u256_div(a, b)`, from any entry locals. -/
theorem u256Div_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w)
    (P : GA → Mem → GA → Prop) :
    AQGD D B A w (fun _ => False) P (fun _ _ _ => False) (fun _ _ _ => True)
      (sourceFunctionBody Guest.guestFn_u256_div) := by
  rw [udBody_eq]
  unfold udBody
  exact aqgd_decCallSpecS (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (_ : Mem) (_ : GA) (L : GA) (_ : Mem) (_ : GA) => U4 (ofString "a") L ∧ U4 (ofString "b") L)
    (RRe := fun _ _ _ _ _ _ => True) (Pc := fun _ _ _ => True) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_u256Divmod_lookup (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => aqgd_conseq (u256Divmod_window hA hU hw) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial))
    (fun _ _ _ _ _ _ _ _ _ _ lookup =>
      let c := callee_u4u4 originalRuntimeCode_u256Divmod_lookup (by decide) lookup; ⟨c.1,c.2.1⟩)
    (fun h => h.elim) (fun _ _ _ _ _ _ _ _ _ => trivial) (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial))
    (fun _ _ _ _ _ _ _ h => h)

#print axioms u256Div_window
end udm
end InitECandidate.Runtime
