import InitECandidate.Runtime.TaylorWindowGD
/-!
The actual `calculate_blob_gas_price` writes only the 640-byte `u256_ws` workspace. `FrameCU` is `FrameC` over the
arena that also pins the `u256_ws` global to `U` (`FrameC` itself, which leaves `u256_ws` free, does not hold for this
function); `blobGasPrice_frameCU` proves it for the actual function.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section bp
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {U : BitVec 64}

/-- Window frame of the actual `calculate_blob_gas_price(excess_blob_gas)`. -/
theorem blobGasPrice_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w)
    (P : GA → Mem → GA → Prop) :
    AQGD D B A w (fun _ => False) P (fun _ _ _ => False) (fun _ _ _ => True)
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price) := by
  have e : sourceFunctionBody Guest.guestFn_calculate_blob_gas_price =
      ProgHOL.decCall (ofString "r") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
        (ofString "taylor_exponential") [ExpHOL.const 1#64, ExpHOL.var VarKind.local (ofString "excess_blob_gas"),
          ExpHOL.const 11684671#64] (ProgHOL.return (ExpHOL.var VarKind.local (ofString "r"))) := by
    unfold sourceFunctionBody
    rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    simp only [Guest.guestFn_calculate_blob_gas_price,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
      Option.map_some,Option.map_none]
  rw [e]
  exact aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ _ _ _ _ _ => True) (RRe := fun _ _ _ _ _ _ => True) (Pc := fun _ _ _ => True)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_taylorExponential_lookup (by simp)
    (fun _ _ _ _ => aqgd_conseq (taylor_window hA hU hw) (fun _ _ _ _ => trivial) (fun _ _ _ h => h.elim)
      (fun _ _ _ h => h))
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun h => h.elim) (fun _ _ _ _ _ _ _ _ _ => trivial)
    (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)) (fun _ _ _ _ _ _ _ h => h)

#print axioms blobGasPrice_window
end bp

/-- The journal/key-buffer arena with the `u256_ws` workspace pointer pinned to `U`. -/
def JWSU (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB U : BitVec 64) (g : GA) : Prop :=
  JWS SP0 P0 FM G0 J C SKB g ∧ WsG U g

/-- `FrameC` over the arena with the `u256_ws` workspace pointer pinned to `U`. -/
def FrameCU (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB U : BitVec 64) (w : BitVec 64) (n : Nat)
    (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (body : ProgHOL 64) : Prop :=
  ∀ (H0 Nj : BitVec 64) (M0 : Mem),
    AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w (fun _ => True)
      (fun _ M G => RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun _ M' G' => ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M' x = M0 x)
      body

section fc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB U : BitVec 64}

/-- Frame contract of the actual `calculate_blob_gas_price` over the pinned-workspace arena: its stores land in the
workspace `[U, U+640)`, which consists of outside words, is not a registry pointer cell, and lies in `Excl`. -/
theorem blobGasPrice_frameCU (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w)
    (hWO : ∀ x, WS U x → Out x ∧ ∀ i, x ≠ c i) (hWE : ∀ x, WS U x → Excl x) :
    FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price) := by
  intro H0 Nj M0 F s code dom aw sl H hH ⟨reg,hM,hHe,hn⟩
  have hA : ∀ g, JWSU SP0 P0 FM G0 J C SKB U g → WsG U g := fun _ h => h.2
  have win : ∀ x, ¬ WS U x →
      (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price)).2.memory x = s.memory x :=
    fun x hx => (blobGasPrice_window (w := x) hA hU hx (fun _ _ _ => True) F s code dom aw (fun _ h => h.elim) H hH
      trivial).1
  obtain ⟨m,a,nrm,r,c1,b1⟩ := blobGasPrice_window (w := w) hA hU hw (fun _ _ _ => True) F s code dom aw
    (fun _ h => h.elim) H hH trivial
  have glob : (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price)).2.globals =
      s.globals :=
    evaluate_keepsGA goodGA goodGA_bodies _ (keepsGA_of_installed originalRuntimeCode_blobGasPrice_lookup (by decide)) s code
  unfold GIs at hH; subst hH
  refine ⟨m,a,fun e => (nrm e).2.choose_spec.2.elim,fun v _ => ⟨s.globals,by unfold GIs; exact glob,?_⟩,c1,b1⟩
  refine ⟨H0,hHe,le_refl _,regT_frame reg (WS U) hWO (fun x hx => win x hx),hn,fun x ho hx => ?_⟩
  have : ¬ WS U x := fun h => hx (hWE x h)
  rw [win x this,hM]

#print axioms blobGasPrice_frameCU
end fc
end InitECandidate.Runtime
