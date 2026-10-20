import InitECandidate.Runtime.U256DivWindowGD
import InitECandidate.Runtime.DivisionHelperGlobalsFrame
import InitECandidate.Runtime.OriginalDivmodCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-- The memory half of an `AQGD` window frame: a single watched word outside
the workspace is preserved by the program in every outcome. -/
theorem aqgd_memory_outside {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop}
 {w : BitVec 64} {Vn : MlS → Prop}
 {P Q : GA → Mem → GA → Prop} {RR : ValueHOL 64 → Mem → GA → Prop} {p : ProgHOL 64}
 (h : AQGD D B A w Vn P Q RR p) {F : Type} (s : PanSemStateFiniteExact 64 F)
 (code : s.code=originalRuntimeCode) (domd : DomD D B s) (Ag : A s.globals)
 (sl : SL Vn s.locals) (Ppre : P s.locals s.memory s.globals) :
 (evaluateHOLFiniteState s p).2.memory w = s.memory w :=
 (h F s code domd Ag sl s.globals rfl Ppre).1

/-- The real `u256_div` preserves every watched word outside the 640-byte
`u256_ws` workspace, from the actual `u256Div_window` source analysis. -/
theorem u256Div_memory_outside_window {F : Type} (s : PanSemStateFiniteExact 64 F)
 (U w : BitVec 64) (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (hU : U.toNat+640≤2^64) (hw : ¬ WS U w) :
 (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_div)).2.memory w=s.memory w := by
 have domd : DomD s.memaddrs s.be s := ⟨domOK,rfl,rfl⟩
 exact aqgd_memory_outside (A := fun g => g=s.globals) (D := s.memaddrs) (B := s.be)
  (Vn := fun _ => False) (w := w) (P := fun _ _ _ => True)
  (u256Div_window (A := fun g => g=s.globals) (U := U) (by intro g hg;subst hg;exact ws) hU hw (fun _ _ _ => True))
  s code domd rfl (by intro x hx;exact hx.elim) trivial

def umBody : ProgHOL 64 :=
 ProgHOL.decCall (ofString "qr") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_divmod") [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.var VarKind.local (ofString "b")] (ProgHOL.return (ExpHOL.rstruct [ExpHOL.rfield 4 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.rfield 5 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.rfield 6 (ExpHOL.var VarKind.local (ofString "qr")), ExpHOL.rfield 7 (ExpHOL.var VarKind.local (ofString "qr"))]))

theorem umBody_eq : sourceFunctionBody Guest.guestFn_u256_mod=umBody := by
 simp only [sourceFunctionBody_eq_structural,umBody,Guest.guestFn_u256_mod]
 rfl

section um
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {U : BitVec 64}
/-- Window frame of the actual `u256_mod(a, b)`, from any entry locals. -/
theorem u256Mod_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat+640≤2^64) (hw : ¬ WS U w)
 (P : GA → Mem → GA → Prop) :
 AQGD D B A w (fun _ => False) P (fun _ _ _ => False) (fun _ _ _ => True)
  (sourceFunctionBody Guest.guestFn_u256_mod) := by
 rw [umBody_eq]
 unfold umBody
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
#print axioms u256Mod_window
end um

/-- The real `u256_mod` preserves every watched word outside the workspace. -/
theorem u256Mod_memory_outside_window {F : Type} (s : PanSemStateFiniteExact 64 F)
 (U w : BitVec 64) (code : s.code=originalRuntimeCode) (domOK : DomOK s.memaddrs)
 (ws : s.globals.lookup (ofString "u256_ws")=some (.val (.word U)))
 (hU : U.toNat+640≤2^64) (hw : ¬ WS U w) :
 (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_u256_mod)).2.memory w=s.memory w := by
 have domd : DomD s.memaddrs s.be s := ⟨domOK,rfl,rfl⟩
 exact aqgd_memory_outside (A := fun g => g=s.globals) (D := s.memaddrs) (B := s.be)
  (Vn := fun _ => False) (w := w) (P := fun _ _ _ => True)
  (u256Mod_window (A := fun g => g=s.globals) (U := U) (by intro g hg;subst hg;exact ws) hU hw (fun _ _ _ => True))
  s code domd rfl (by intro x hx;exact hx.elim) trivial
#print axioms aqgd_memory_outside
#print axioms u256Div_memory_outside_window
#print axioms u256Mod_memory_outside_window
end InitECandidate.Runtime
