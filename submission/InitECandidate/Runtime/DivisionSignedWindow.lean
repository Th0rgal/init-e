import InitECandidate.Runtime.DivisionHelperWindow
import InitECandidate.Runtime.VmFn_u256_abs
import InitECandidate.Runtime.VmFn_u256_neg
import InitECandidate.Runtime.DigitsDivmodGD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem mf_u256_abs : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_abs) :=
 memoryFrame_of_good vmLookup_u256_abs (by decide) (by decide)
theorem nb_u256_abs : noTopBreak (sourceFunctionBody Guest.guestFn_u256_abs) = true := by body_check Guest.guestFn_u256_abs
theorem nc_u256_abs : noTopContinue (sourceFunctionBody Guest.guestFn_u256_abs) = true := by body_check Guest.guestFn_u256_abs
theorem mf_u256_neg : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_neg) :=
 memoryFrame_of_good vmLookup_u256_neg (by decide) (by decide)

/-- One `u256_abs` declaration call: with `True` as both precondition and postcondition the
callee only has to keep memory and globals, which its read-only body does. -/
theorem aqgd_decCall_abs {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
 {RR : ValueHOL 64 → Mem → GA → Prop} (name : MlS) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
 (hc : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => False) RR cont) :
 AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => False) RR
  (.decCall name (.comb [.one,.one,.one,.one]) (ofString "u256_abs") arguments cont) :=
 aqgd_decCallSpecS (Pe := fun L M H _ M' H' => M'=M ∧ H'=H) (RRe := fun L M H _ M' H' => M'=M ∧ H'=H)
  (Pc := fun _ _ _ => True) (Qc := fun _ _ _ => False)
  _ _ _ _ _ _ _ vmLookup_u256_abs (fun _ _ _ _ _ h => h.elim)
  (fun L0 M0 H0 _ => aqgd_of_mf mf_u256_abs nb_u256_abs nc_u256_abs M0 H0)
  (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) (fun _ _ _ _ _ _ _ _ _ => trivial) hc
  (fun _ _ _ _ _ _ _ h => h.elim)
#print axioms aqgd_decCall_abs

/-- The sign-fixing tail shared by `u256_sdiv`/`u256_smod`: a conditional tail call to the
read-only `u256_neg` followed by the return. -/
theorem aqgd_signed_tail {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}
 (condition : ExpHOL 64) (arg : MlS) (out : ExpHOL 64) :
 AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True)
  (.seq (.ite condition (.call none (ofString "u256_neg") [.var .local arg]) .skip) (.return out)) := by
 have hneg : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
   (.call none (ofString "u256_neg") [.var .local arg]) :=
  aqgd_tailCall_mf (ofString "u256_neg") [.var .local arg]
   [(ofString "a",.comb [.one,.one,.one,.one])] (sourceFunctionBody Guest.guestFn_u256_neg)
   (.comb [.one,.one,.one,.one]) vmLookup_u256_neg mf_u256_neg (fun _ _ _ _ _ => trivial)
 have hneg' : AQGD D B A w (fun _ => False) (fun L M H => True ∧ True) (fun _ _ _ => True) (fun _ _ _ => True)
   (.call none (ofString "u256_neg") [.var .local arg]) :=
  aqgd_conseq hneg (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
 have hskip : AQGD D B A w (fun _ => False) (fun L M H => True ∧ True) (fun _ _ _ => True) (fun _ _ _ => True) .skip :=
  aqgd_conseq (aqgd_skip (P := fun _ _ _ => True) (RR := fun _ _ _ => True)) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
 have hite : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
   (.ite condition (.call none (ofString "u256_neg") [.var .local arg]) .skip) :=
  aqgd_ite condition (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) hneg' hskip
 exact aqgd_seq hite (aqgd_return out (fun _ _ _ _ _ _ _ _ => trivial))
#print axioms aqgd_signed_tail
def sdivCondA : ExpHOL 64 :=
 ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.or [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "b")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "b"))]) (ExpHOL.const 0)

def sdivCondB : ExpHOL 64 :=
 ExpHOL.cmp Cmp.equal (ExpHOL.shift Shift.lsr (ExpHOL.op BinOp.xor [ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "a")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "b"))]) (ExpHOL.const 63)) (ExpHOL.const 1)

def sdivBody : ProgHOL 64 :=
 ProgHOL.seq
  (ProgHOL.ite sdivCondA (ProgHOL.return (ExpHOL.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0])) ProgHOL.skip)
  (ProgHOL.decCall (ofString "aa") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_abs") [ExpHOL.var VarKind.local (ofString "a")]
    (ProgHOL.decCall (ofString "bb") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_abs") [ExpHOL.var VarKind.local (ofString "b")]
      (ProgHOL.decCall (ofString "q") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_div") [ExpHOL.var VarKind.local (ofString "aa"), ExpHOL.var VarKind.local (ofString "bb")]
        (ProgHOL.seq
          (ProgHOL.ite sdivCondB (ProgHOL.call none (ofString "u256_neg") [ExpHOL.var VarKind.local (ofString "q")]) ProgHOL.skip)
          (ProgHOL.return (ExpHOL.var VarKind.local (ofString "q")))))))

theorem sdivBody_eq : sourceFunctionBody Guest.guestFn_u256_sdiv=sdivBody := by
 simp only [sourceFunctionBody_eq_structural,sdivBody,sdivCondA,sdivCondB,Guest.guestFn_u256_sdiv]
 rfl

section sdm
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {U : BitVec 64}
/-- Window frame of the actual `u256_sdiv(a, b)`, composed from its real callees:
`u256_abs` is read-only, `u256_div` keeps every word outside the workspace, and the
sign-fixing tail is a conditional tail call to the read-only `u256_neg`. -/
theorem u256Sdiv_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat+640≤2^64) (hw : ¬ WS U w)
 (P : GA → Mem → GA → Prop) :
 AQGD D B A w (fun _ => False) P (fun _ _ _ => False) (fun _ _ _ => True)
  (sourceFunctionBody Guest.guestFn_u256_sdiv) := by
 rw [sdivBody_eq]
 unfold sdivBody
 have hret0 : AQGD D B A w (fun _ => False) (fun L M H => True ∧ True) (fun _ _ _ => True) (fun _ _ _ => True)
   (.return (.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0])) :=
  aqgd_conseq (aqgd_return (Q := fun _ _ _ => True) (RR := fun _ _ _ => True) (.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0]) (fun _ _ _ _ _ _ _ _ => trivial))
   (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
 have hskip0 : AQGD D B A w (fun _ => False) (fun L M H => True ∧ True) (fun _ _ _ => True) (fun _ _ _ => True) .skip :=
  aqgd_conseq (aqgd_skip (P := fun _ _ _ => True) (RR := fun _ _ _ => True))
   (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
 have hite : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
   (.ite sdivCondA (.return (.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0])) .skip) :=
  aqgd_ite sdivCondA (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) hret0 hskip0
 have hdiv : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True)
   (.decCall (ofString "q") (.comb [.one,.one,.one,.one]) (ofString "u256_div")
     [ExpHOL.var VarKind.local (ofString "aa"), ExpHOL.var VarKind.local (ofString "bb")]
     (.seq (.ite sdivCondB (.call none (ofString "u256_neg") [ExpHOL.var VarKind.local (ofString "q")]) .skip)
       (.return (ExpHOL.var VarKind.local (ofString "q"))))) :=
  aqgd_decCallSpecS (Pe := fun _ _ _ _ _ _ => True) (RRe := fun _ _ _ _ _ _ => True)
   (Pc := fun _ _ _ => True) (Qc := fun _ _ _ => False)
   _ _ _ _ _ _ _ vmLookup_u256_div (fun _ _ _ _ _ h => h.elim)
   (fun _ _ _ _ => aqgd_conseq (u256Div_window hA hU hw _) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
     (fun _ _ _ _ => trivial))
   (by intros; trivial) (fun h => h.elim) (by intros; trivial)
   (aqgd_signed_tail sdivCondB (ofString "q") (.var .local (ofString "q")))
   (fun _ _ _ _ _ _ _ h => h.elim)
 have hbb := aqgd_decCall_abs (Vn := fun _ => False) (D := D) (B := B) (A := A) (w := w) (ofString "bb")
   [ExpHOL.var VarKind.local (ofString "b")] hdiv
 have haa := aqgd_decCall_abs (Vn := fun _ => False) (D := D) (B := B) (A := A) (w := w) (ofString "aa")
   [ExpHOL.var VarKind.local (ofString "a")] hbb
 exact aqgd_conseq (aqgd_seq hite haa) (fun _ _ _ _ => trivial) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
#print axioms u256Sdiv_window
end sdm

def smodCondB : ExpHOL 64 :=
 ExpHOL.cmp Cmp.equal (ExpHOL.shift Shift.lsr (ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "a"))) (ExpHOL.const 63)) (ExpHOL.const 1)

def smodBody : ProgHOL 64 :=
 ProgHOL.seq
  (ProgHOL.ite sdivCondA (ProgHOL.return (ExpHOL.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0])) ProgHOL.skip)
  (ProgHOL.decCall (ofString "aa") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_abs") [ExpHOL.var VarKind.local (ofString "a")]
    (ProgHOL.decCall (ofString "bb") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_abs") [ExpHOL.var VarKind.local (ofString "b")]
      (ProgHOL.decCall (ofString "r") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_mod") [ExpHOL.var VarKind.local (ofString "aa"), ExpHOL.var VarKind.local (ofString "bb")]
        (ProgHOL.seq
          (ProgHOL.ite smodCondB (ProgHOL.call none (ofString "u256_neg") [ExpHOL.var VarKind.local (ofString "r")]) ProgHOL.skip)
          (ProgHOL.return (ExpHOL.var VarKind.local (ofString "r")))))))

theorem smodBody_eq : sourceFunctionBody Guest.guestFn_u256_smod=smodBody := by
 simp only [sourceFunctionBody_eq_structural,smodBody,sdivCondA,smodCondB,Guest.guestFn_u256_smod]
 rfl

section smd
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {U : BitVec 64}
/-- Window frame of the actual `u256_smod(a, b)`, composed from `u256_abs` (read-only),
`u256_mod` (workspace-only) and the conditional tail call to `u256_neg`. -/
theorem u256Smod_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat+640≤2^64) (hw : ¬ WS U w)
 (P : GA → Mem → GA → Prop) :
 AQGD D B A w (fun _ => False) P (fun _ _ _ => False) (fun _ _ _ => True)
  (sourceFunctionBody Guest.guestFn_u256_smod) := by
 rw [smodBody_eq]
 unfold smodBody
 have hret0 : AQGD D B A w (fun _ => False) (fun L M H => True ∧ True) (fun _ _ _ => True) (fun _ _ _ => True)
   (.return (.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0])) :=
  aqgd_conseq (aqgd_return (Q := fun _ _ _ => True) (RR := fun _ _ _ => True)
    (.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0]) (fun _ _ _ _ _ _ _ _ => trivial))
   (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
 have hskip0 : AQGD D B A w (fun _ => False) (fun L M H => True ∧ True) (fun _ _ _ => True) (fun _ _ _ => True) .skip :=
  aqgd_conseq (aqgd_skip (P := fun _ _ _ => True) (RR := fun _ _ _ => True))
   (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
 have hite : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
   (.ite sdivCondA (.return (.rstruct [ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0, ExpHOL.const 0])) .skip) :=
  aqgd_ite sdivCondA (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) hret0 hskip0
 have hmod : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True)
   (.decCall (ofString "r") (.comb [.one,.one,.one,.one]) (ofString "u256_mod")
     [ExpHOL.var VarKind.local (ofString "aa"), ExpHOL.var VarKind.local (ofString "bb")]
     (.seq (.ite smodCondB (.call none (ofString "u256_neg") [ExpHOL.var VarKind.local (ofString "r")]) .skip)
       (.return (ExpHOL.var VarKind.local (ofString "r"))))) :=
  aqgd_decCallSpecS (Pe := fun _ _ _ _ _ _ => True) (RRe := fun _ _ _ _ _ _ => True)
   (Pc := fun _ _ _ => True) (Qc := fun _ _ _ => False)
   _ _ _ _ _ _ _ vmLookup_u256_mod (fun _ _ _ _ _ h => h.elim)
   (fun _ _ _ _ => aqgd_conseq (u256Mod_window hA hU hw _) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
     (fun _ _ _ _ => trivial))
   (by intros; trivial) (fun h => h.elim) (by intros; trivial)
   (aqgd_signed_tail smodCondB (ofString "r") (.var .local (ofString "r")))
   (fun _ _ _ _ _ _ _ h => h.elim)
 have hbb := aqgd_decCall_abs (Vn := fun _ => False) (D := D) (B := B) (A := A) (w := w) (ofString "bb")
   [ExpHOL.var VarKind.local (ofString "b")] hmod
 have haa := aqgd_decCall_abs (Vn := fun _ => False) (D := D) (B := B) (A := A) (w := w) (ofString "aa")
   [ExpHOL.var VarKind.local (ofString "a")] hbb
 exact aqgd_conseq (aqgd_seq hite haa) (fun _ _ _ _ => trivial) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
#print axioms u256Smod_window
end smd

/-- The real `u256_sdiv` preserves every watched word outside the workspace. -/
theorem u256Sdiv_memory_outside_window {F : Type} (s : PanSemStateFiniteExact 64 F)
 (U w : BitVec 64) (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (hU : U.toNat+640≤2^64) (hw : ¬ WS U w) :
 (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_sdiv)).2.memory w=s.memory w := by
 have domd : DomD s.memaddrs s.be s := ⟨domOK,rfl,rfl⟩
 exact aqgd_memory_outside (A := fun g => g=s.globals) (D := s.memaddrs) (B := s.be)
  (Vn := fun _ => False) (w := w) (P := fun _ _ _ => True)
  (u256Sdiv_window (A := fun g => g=s.globals) (U := U) (by intro g hg;subst hg;exact ws) hU hw (fun _ _ _ => True))
  s code domd rfl (by intro x hx;exact hx.elim) trivial

/-- The real `u256_smod` preserves every watched word outside the workspace. -/
theorem u256Smod_memory_outside_window {F : Type} (s : PanSemStateFiniteExact 64 F)
 (U w : BitVec 64) (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (hU : U.toNat+640≤2^64) (hw : ¬ WS U w) :
 (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_smod)).2.memory w=s.memory w := by
 have domd : DomD s.memaddrs s.be s := ⟨domOK,rfl,rfl⟩
 exact aqgd_memory_outside (A := fun g => g=s.globals) (D := s.memaddrs) (B := s.be)
  (Vn := fun _ => False) (w := w) (P := fun _ _ _ => True)
  (u256Smod_window (A := fun g => g=s.globals) (U := U) (by intro g hg;subst hg;exact ws) hU hw (fun _ _ _ => True))
  s code domd rfl (by intro x hx;exact hx.elim) trivial
#print axioms u256Sdiv_memory_outside_window
#print axioms u256Smod_memory_outside_window
/-- The complete honest effect description of the four real division helpers: on a
well-formed state with `u256_ws = some (word U)`, every watched word outside the
640-byte workspace is preserved. -/
theorem division_helper_memory_outside_window (kind : DivisionOpcodeKind) {F : Type}
 (s : PanSemStateFiniteExact 64 F) (U w : BitVec 64) (code : s.code=originalRuntimeCode)
 (domOK : DomOK s.memaddrs) (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (hU : U.toNat+640≤2^64) (hw : ¬ WS U w) :
 (evaluateHOLFiniteState s (divisionHelperBody kind)).2.memory w=s.memory w := by
 cases kind with
 | div=>exact u256Div_memory_outside_window s U w code domOK ws hU hw
 | sdiv=>exact u256Sdiv_memory_outside_window s U w code domOK ws hU hw
 | mod=>exact u256Mod_memory_outside_window s U w code domOK ws hU hw
 | smod=>exact u256Smod_memory_outside_window s U w code domOK ws hU hw
#print axioms division_helper_memory_outside_window
end InitECandidate.Runtime
