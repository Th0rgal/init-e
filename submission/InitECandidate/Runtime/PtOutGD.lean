import InitECandidate.Runtime.PtRestGD
/-!
Threading the interpreter output record through the `process_transaction` suffix: `LPSo Y Ix` is `LPS Ix` together
with the local `out = Y` (no statement of the suffix assigns `out`). The update/restore lemmas take the `sender`
inequality together with the `out` inequality, so every suffix step carries over with the same arguments.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- `LPS` with the interpreter output record pointer `out = Y`. -/
def LPSo (Y Ix : BitVec 64) (L : GA) : Prop :=
  LPS Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))

theorem lpso_upd {Y Ix : BitVec 64} {L : GA} (h : LPSo Y Ix L) (name : MlS) (v : ValueHOL 64)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out") :
    LPSo Y Ix (L.update (name,v)) :=
  ⟨lps_upd h.1 name v ne ne'.1,by rw [lookup_update_ne' _ _ (Ne.symm ne'.2)]; exact h.2⟩

theorem lpso_res {Y Ix : BitVec 64} {L : GA} (h : LPSo Y Ix L) (name : MlS) (o : Option (ValueHOL 64))
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out") :
    LPSo Y Ix (L.resVarEq (name,o)) :=
  ⟨lps_res h.1 name o ne ne'.1,by rw [resVarEq_lookup_ne' _ _ _ _ (Ne.symm ne'.2)]; exact h.2⟩

section pxh
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {X : Mem → GA → Prop} {QM : Mem → GA → Prop} {Ix Y : BitVec 64}

theorem aqgd_dec_lpso (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPSo Y Ix L ∧ X M G) (fun _ M G => QM M G) RR body) :
    AQGD D B A w (fun _ => False) (fun L M G => LPSo Y Ix L ∧ X M G) (fun _ M G => QM M G) RR
      (.dec name shape init body) :=
  aqgd_dec _ _ _ (fun h => h.elim) (fun _ v _ _ _ pre _ _ _ => ⟨lpso_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => h)

theorem aqgd_decCall_lpso (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPSo Y Ix L ∧ X M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B A w (fun _ => False) (fun L M G => LPSo Y Ix L ∧ X M G) (fun _ M G => QM M G) RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ installed mf nb nc (fun _ _ _ v pre => ⟨lpso_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => h)

theorem aqgd_decCall_lpsoR (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    {cont : ProgHOL 64} (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender" ∧ name ≠ ofString "out")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPSo Y Ix L ∧ X M G) (fun L M G => LPSo Y Ix L ∧ X M G) RR
      cont) :
    AQGD D B A w (fun _ => False) (fun L M G => LPSo Y Ix L ∧ X M G) (fun L M G => LPSo Y Ix L ∧ X M G) RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ installed mf nb nc (fun _ _ _ v pre => ⟨lpso_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => ⟨lpso_res h.1 _ _ ne ne',h.2⟩)

#print axioms aqgd_dec_lpso
#print axioms aqgd_decCall_lpso
#print axioms aqgd_decCall_lpsoR
end pxh
end InitECandidate.Runtime
