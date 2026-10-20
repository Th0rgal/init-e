import InitECandidate.Runtime.EncWriters2GD
import InitECandidate.Runtime.VmFn_u256_byte_length
import InitECandidate.Runtime.VmFn_u256_limb
/-!
Fenced window spec of the actual `u256_to_be_min`: an ascending byte loop at `out + i` whose cursor stays at most
`DF + 8` by the domain facts of its stores.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def tbBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "len") ShapeHOL.one (ofString "u256_byte_length") [ExpHOL.var VarKind.local (ofString "a")] (ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "len"))) (ProgHOL.dec (ofString "pos") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "len"), ExpHOL.const 1#64], ExpHOL.var VarKind.local (ofString "i")]) (ProgHOL.decCall (ofString "l") ShapeHOL.one (ofString "u256_limb") [ExpHOL.var VarKind.local (ofString "a"), ExpHOL.shift Shift.lsr (ExpHOL.var VarKind.local (ofString "pos")) (ExpHOL.const 3#64)] (ProgHOL.seq (ProgHOL.storeByte (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.op BinOp.and [ExpHOL.shift Shift.lsr (ExpHOL.var VarKind.local (ofString "l")) (ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "pos"), ExpHOL.const 7#64], ExpHOL.const 8#64]), ExpHOL.const 255#64])) (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])))))) (ProgHOL.return (ExpHOL.var VarKind.local (ofString "len")))))

theorem tbBody_eq : sourceFunctionBody Guest.guestFn_u256_to_be_min = tbBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_u256_to_be_min,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl


theorem nb_u256_byte_length : noTopBreak (sourceFunctionBody Guest.guestFn_u256_byte_length) = true := by
  body_check Guest.guestFn_u256_byte_length
theorem nc_u256_byte_length : noTopContinue (sourceFunctionBody Guest.guestFn_u256_byte_length) = true := by
  body_check Guest.guestFn_u256_byte_length
theorem nb_u256_limb : noTopBreak (sourceFunctionBody Guest.guestFn_u256_limb) = true := by
  body_check Guest.guestFn_u256_limb
theorem nc_u256_limb : noTopContinue (sourceFunctionBody Guest.guestFn_u256_limb) = true := by
  body_check Guest.guestFn_u256_limb

/-- Cursor invariant of `u256_to_be_min`: `out = O`, `i = I` with `O + I ≤ DF + 8`. -/
def TbI (DF : Nat) (O : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "out") = some (.val (.word O)) ∧
    ∃ I : BitVec 64, L.lookup (ofString "i") = some (.val (.word I)) ∧ O.toNat + I.toNat ≤ DF + 8

theorem tbI_upd {DF : Nat} {O : BitVec 64} {L : GA} (h : TbI DF O L) (name : MlS) (v : ValueHOL 64)
    (h1 : ofString "out" ≠ name) (h2 : ofString "i" ≠ name) : TbI DF O (L.update (name,v)) :=
  let ⟨ho,I,hi,hb⟩ := h
  ⟨by rw [lookup_update_ne' _ _ h1]; exact ho,I,by rw [lookup_update_ne' _ _ h2]; exact hi,hb⟩

theorem tbI_res {DF : Nat} {O : BitVec 64} {L : GA} (h : TbI DF O L) (name : MlS) (o : Option (ValueHOL 64))
    (h1 : ofString "out" ≠ name) (h2 : ofString "i" ≠ name) : TbI DF O (L.resVarEq (name,o)) :=
  let ⟨ho,I,hi,hb⟩ := h
  ⟨by rw [resVarEq_lookup_ne' _ _ _ _ h1]; exact ho,I,by rw [resVarEq_lookup_ne' _ _ _ _ h2]; exact hi,hb⟩

section tb
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {DF : Nat}

/-- The actual `u256_to_be_min(a, out)` writes only at or above `out` (given `out ≤ DF + 8`). -/
theorem toBeMin_win (hF : Fence D DF) (hDF : DF ≤ 2 ^ 62) (Lo : BitVec 64) (hLo8 : Lo.toNat % 8 = 0)
    (hw : w.toNat < Lo.toNat) (O : BitVec 64) (hO : Lo.toNat ≤ O.toNat) (hO8 : O.toNat ≤ DF + 8) :
    AQGD D B A w (fun _ => False) (fun L _ _ => L.lookup (ofString "out") = some (.val (.word O)))
      (fun _ _ _ => False) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_u256_to_be_min) := by
  rw [tbBody_eq]; unfold tbBody
  refine r_decCall (LB := fun L => L.lookup (ofString "out") = some (.val (.word O))) (LQ' := fun _ => False)
    _ _ _ _ _ _ _ vmLookup_u256_byte_length
    (memoryFrame_of_good vmLookup_u256_byte_length (by decide) (by decide)) nb_u256_byte_length nc_u256_byte_length
    (fun h => h.elim) (fun L v ho _ => by rw [lookup_update_ne' _ _ (by decide)]; exact ho) ?_ (fun _ _ _ h => h)
  refine r_dec (LB := TbI DF O) (LQ' := fun _ => False) _ _ _ (fun h => h.elim) ?_ ?_ (fun _ _ _ h => h)
  · intro F s v _ ho ev
    simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,0,lookup_update_eq' _ _ _,by simp; omega⟩
  refine aqgd_seq (r_while (LC := fun _ => True) _ (fun _ _ _ _ _ _ => trivial) ?_)
    (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial))
  refine aqgd_conseq (P := fun L _ _ => TbI DF O L) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine r_dec (LB := TbI DF O) (LQ' := TbI DF O) _ _ _ (fun h => h.elim)
    (fun s v _ lp _ => tbI_upd lp _ v (by decide) (by decide)) ?_ (fun _ _ _ h => tbI_res h _ _ (by decide) (by decide))
  refine r_decCall (LB := TbI DF O) (LQ' := TbI DF O) _ _ _ _ _ _ _ vmLookup_u256_limb
    (memoryFrame_of_good vmLookup_u256_limb (by decide) (by decide)) nb_u256_limb nc_u256_limb
    (fun h => h.elim) (fun L v lp _ => tbI_upd lp _ v (by decide) (by decide)) ?_
    (fun _ _ _ h => tbI_res h _ _ (by decide) (by decide))
  refine aqgd_seq (r_stb (LP := TbI DF O) (LQ := fun L => TbI DF O L ∧ ∀ I : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word I)) → O.toNat + I.toNat + 1 ≤ DF + 8) Lo hLo8 hw _ _ ?_) ?_
  · intro F s _ ⟨ho,I,hi,hb⟩
    have e : (O + I).toNat = O.toNat + I.toNat := by simp [BitVec.toNat_add]; omega
    refine ⟨O + I,by simp [EV,evalHOLExact,evalListHOLExact,ho,hi,wordOpHOL,wordOp,valueIsWord,valueWord],by omega,
      fun hD => ⟨⟨ho,I,hi,hb⟩,fun I' hi' => by
        rw [hi] at hi'; simp at hi'; subst hi'; have := fence_byte hF hD; omega⟩⟩
  refine r_assign _ _ (fun s v _ ⟨⟨ho,I,hi,hb⟩,hk⟩ ev => ?_)
  simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev; subst ev
  have h2 := hk I hi
  have e : (I + 1#64).toNat = I.toNat + 1 := by simp [BitVec.toNat_add]; omega
  exact ⟨by rw [lookup_update_ne' _ _ (by decide)]; exact ho,_,lookup_update_eq' _ _ _,by rw [e]; omega⟩

#print axioms toBeMin_win
end tb
end InitECandidate.Runtime
