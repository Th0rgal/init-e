import InitECandidate.Runtime.U256DivWindowGD
import InitECandidate.Runtime.VmFn_u256_from_word
import InitECandidate.Runtime.VmFn_u256_mul
import InitECandidate.Runtime.VmFn_u256_mul_full
import InitECandidate.Runtime.OriginalTrapCode
/-!
Window frame of the actual `taylor_exponential`: its only memory writer is `u256_div`, whose stores land in the
640-byte `u256_ws` workspace. Includes a discarded-call rule for memory-frame callees with any body outcome.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section ty
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {U : BitVec 64}

/-- A discarded call to a memory-and-globals-keeping function with one-word parameters. -/
theorem aqgd_call_x {X : Mem → GA → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (mf : MemoryFrame body) (nb : noTopBreak body = true)
    (nc : noTopContinue body = true) :
    AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => X M G) RR
      (.call (some (none,none)) function arguments) :=
  aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    _ _ _ _ _ installed allOne (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun _ _ _ _ _ _ pre ⟨e1,e2⟩ => by rw [e1,e2]; exact pre)

/-- A discarded call to a memory-and-globals-keeping function (any body outcome). -/
theorem aqgd_call_mfAny {X : Mem → GA → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) :
    AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => X M G) RR
      (.call (some (none,none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  split
  · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing]
  · rename_i values args
    split
    · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing]
    · rename_i found callee foundShape lookup
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split
      · refine ⟨rfl,fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing]
      · obtain ⟨mm,gg⟩ := mf (callEntryStateHOLFinite state callee) code
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at mm gg
          change bodyPost.memory = state.memory at mm
          change bodyPost.globals = state.globals at gg
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals (try split)
          all_goals first
            | exact ⟨by simp [mm],fun _ => by simp [gg]; exact aw,
                fun _ => ⟨sl,H,by unfold GIs; simp [gg]; exact hH,by simp [mm]; exact pre⟩,
                (fun v e => by cases e),by simp,by simp⟩
            | (refine ⟨by simp [mm,emptyLocalsHOLFinite],fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;>
                simp_all [Continuing])
            | (refine ⟨by simp [mm],fun h => ?_,fun e => ?_,fun v e => ?_,?_,?_⟩ <;> simp_all [Continuing])

#print axioms aqgd_call_mfAny

/-- `x = u256_div(a, b)` keeps a watched word outside the workspace. -/
theorem aqgd_callAssign_div (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64)
    (hw : ¬ WS U w) (name : MlS) (arguments : List (ExpHOL 64)) :
    AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => True) RR
      (.call (some (some (.local,name),none)) (ofString "u256_div") arguments) :=
  aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun _ _ _ _ _ _ => True) (RRe := fun _ _ _ _ _ _ => True)
    _ _ _ _ _ _ originalRuntimeCode_u256Div_lookup (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun _ _ _ _ => aqgd_conseq (u256Div_window hA hU hw _) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial))
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial)

#print axioms aqgd_callAssign_div

theorem nb_u256_mul : noTopBreak (sourceFunctionBody Guest.guestFn_u256_mul) = true := by body_check Guest.guestFn_u256_mul
theorem nc_u256_mul : noTopContinue (sourceFunctionBody Guest.guestFn_u256_mul) = true := by body_check Guest.guestFn_u256_mul
theorem mf_u256_mul : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_mul) := memoryFrame_of_good vmLookup_u256_mul (by decide) (by decide)
theorem nb_u256_add : noTopBreak (sourceFunctionBody Guest.guestFn_u256_add) = true := by body_check Guest.guestFn_u256_add
theorem nc_u256_add : noTopContinue (sourceFunctionBody Guest.guestFn_u256_add) = true := by body_check Guest.guestFn_u256_add
theorem mf_u256_add : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_add) := memoryFrame_of_good originalRuntimeCode_u256Add_lookup (by decide) (by decide)
theorem nb_u256_mul_full : noTopBreak (sourceFunctionBody Guest.guestFn_u256_mul_full) = true := by body_check Guest.guestFn_u256_mul_full
theorem nc_u256_mul_full : noTopContinue (sourceFunctionBody Guest.guestFn_u256_mul_full) = true := by body_check Guest.guestFn_u256_mul_full
theorem mf_u256_mul_full : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_mul_full) := memoryFrame_of_good vmLookup_u256_mul_full (by decide) (by decide)
theorem nb_u256_is_zero : noTopBreak (sourceFunctionBody Guest.guestFn_u256_is_zero) = true := by body_check Guest.guestFn_u256_is_zero
theorem nc_u256_is_zero : noTopContinue (sourceFunctionBody Guest.guestFn_u256_is_zero) = true := by body_check Guest.guestFn_u256_is_zero
theorem mf_u256_is_zero : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_is_zero) := memoryFrame_of_good originalRuntimeCode_u256IsZero_lookup (by decide) (by decide)
theorem nb_u256_from_word : noTopBreak (sourceFunctionBody Guest.guestFn_u256_from_word) = true := by body_check Guest.guestFn_u256_from_word
theorem nc_u256_from_word : noTopContinue (sourceFunctionBody Guest.guestFn_u256_from_word) = true := by body_check Guest.guestFn_u256_from_word
theorem mf_u256_from_word : MemoryFrame (sourceFunctionBody Guest.guestFn_u256_from_word) := memoryFrame_of_good vmLookup_u256_from_word (by decide) (by decide)
theorem mf_trap_with : MemoryFrame (sourceFunctionBody Guest.guestFn_trap_with) := memoryFrame_of_good originalRuntimeCode_trap_lookup (by decide) (by decide)

def tyLoop : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "out"), none)) (ofString "u256_add") [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.var VarKind.local (ofString "acc")]) (ProgHOL.decCall (ofString "prod") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_mul_full") [ExpHOL.var VarKind.local (ofString "acc"), ExpHOL.var VarKind.local (ofString "num")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.op BinOp.or [ExpHOL.rfield 4 (ExpHOL.var VarKind.local (ofString "prod")), ExpHOL.rfield 5 (ExpHOL.var VarKind.local (ofString "prod")), ExpHOL.rfield 6 (ExpHOL.var VarKind.local (ofString "prod")), ExpHOL.rfield 7 (ExpHOL.var VarKind.local (ofString "prod"))]) (ExpHOL.const 0#64)) (ProgHOL.call (some (none, none)) (ofString "trap_with") [ExpHOL.const 3#64]) ProgHOL.skip) (ProgHOL.dec (ofString "p") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.rstruct [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "prod")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "prod")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "prod")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "prod"))]) (ProgHOL.decCall (ofString "di") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_from_word") [ExpHOL.var VarKind.local (ofString "i")] (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "di"), none)) (ofString "u256_mul") [ExpHOL.var VarKind.local (ofString "di"), ExpHOL.var VarKind.local (ofString "den")]) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "acc"), none)) (ofString "u256_div") [ExpHOL.var VarKind.local (ofString "p"), ExpHOL.var VarKind.local (ofString "di")]) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64])) (ProgHOL.call (some (some (VarKind.local, ofString "nz"), none)) (ofString "u256_is_zero") [ExpHOL.var VarKind.local (ofString "acc")]))))))))

def tyBody : ProgHOL 64 :=
  ProgHOL.decCall (ofString "den") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_from_word") [ExpHOL.var VarKind.local (ofString "denominator")] (ProgHOL.decCall (ofString "num") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_from_word") [ExpHOL.var VarKind.local (ofString "numerator")] (ProgHOL.decCall (ofString "acc") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_from_word") [ExpHOL.var VarKind.local (ofString "factor")] (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "acc"), none)) (ofString "u256_mul") [ExpHOL.var VarKind.local (ofString "acc"), ExpHOL.var VarKind.local (ofString "den")]) (ProgHOL.dec (ofString "out") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.rstruct [ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64]) (ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.const 1#64) (ProgHOL.dec (ofString "zero") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.rstruct [ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64]) (ProgHOL.decCall (ofString "nz") ShapeHOL.one (ofString "u256_is_zero") [ExpHOL.var VarKind.local (ofString "acc")] (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "nz")) (ExpHOL.const 0#64)) tyLoop) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "out"), none)) (ofString "u256_div") [ExpHOL.var VarKind.local (ofString "out"), ExpHOL.var VarKind.local (ofString "den")]) (ProgHOL.return (ExpHOL.var VarKind.local (ofString "out"))))))))))))

theorem tyBody_eq : sourceFunctionBody Guest.guestFn_taylor_exponential = tyBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_taylor_exponential,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl

theorem tyLoop_aqgd (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w) :
    AQGD D B A w (fun _ => False) (fun _ M G => (fun _ _ => True) M G) (fun _ M G => (fun _ _ => True) M G)
      (fun _ _ _ => True) tyLoop := by
  unfold tyLoop
  have fw' := fun {cont : ProgHOL 64} (name : MlS) (args : List (ExpHOL 64))
      (h : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) cont) =>
    aqgd_decCall_x (X := fun _ _ => True) (Q := fun _ _ => True) name (ofString "u256_from_word")
      (.comb [.one,.one,.one,.one]) args _ _ _ vmLookup_u256_from_word mf_u256_from_word nb_u256_from_word
      nc_u256_from_word h
  refine aqgd_seq (aqgd_callAssign_x (X := fun _ _ => True) _ _ _ _ _ _ originalRuntimeCode_u256Add_lookup mf_u256_add nb_u256_add nc_u256_add) ?_
  refine aqgd_decCall_x (X := fun _ _ => True) (Q := fun _ _ => True) _ _ _ _ _ _ _ vmLookup_u256_mul_full mf_u256_mul_full nb_u256_mul_full nc_u256_mul_full ?_
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqgd_conseq (aqgd_call_mfAny (X := fun _ _ => True) _ _ _ _ _ originalRuntimeCode_trap_lookup mf_trap_with)
      (fun _ _ _ _ => trivial) (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_conseq aqgd_skip (fun _ _ _ _ => trivial) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  refine aqgd_dec_x (X := fun _ _ => True) (Q := fun _ _ => True) _ _ _ ?_
  refine fw' _ _ ?_
  refine aqgd_seq (aqgd_callAssign_x (X := fun _ _ => True) _ _ _ _ _ _ vmLookup_u256_mul mf_u256_mul nb_u256_mul nc_u256_mul) ?_
  refine aqgd_seq (aqgd_callAssign_div hA hU hw _ _) ?_
  refine aqgd_seq (aqgd_assign_x (X := fun _ _ => True) _ _) ?_
  exact aqgd_callAssign_x (X := fun _ _ => True) _ _ _ _ _ _ originalRuntimeCode_u256IsZero_lookup mf_u256_is_zero nb_u256_is_zero nc_u256_is_zero

#print axioms tyLoop_aqgd

/-- Window frame of the actual `taylor_exponential(factor, numerator, denominator)`. -/
theorem taylor_window (hA : ∀ g, A g → WsG U g) (hU : U.toNat + 640 ≤ 2 ^ 64) (hw : ¬ WS U w) :
    AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True)
      (sourceFunctionBody Guest.guestFn_taylor_exponential) := by
  rw [tyBody_eq]
  unfold tyBody
  have fw := fun {cont : ProgHOL 64} (name : MlS) (args : List (ExpHOL 64))
      (h : AQGD D B A w (fun _ => False) (fun _ _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True) cont) =>
    aqgd_decCall_x (X := fun _ _ => True) (Q := fun _ _ => False) name (ofString "u256_from_word")
      (.comb [.one,.one,.one,.one]) args _ _ _ vmLookup_u256_from_word mf_u256_from_word nb_u256_from_word nc_u256_from_word h
  refine fw _ _ (fw _ _ (fw _ _ ?_))
  refine aqgd_seq (aqgd_callAssign_x (X := fun _ _ => True) _ _ _ _ _ _ vmLookup_u256_mul mf_u256_mul nb_u256_mul nc_u256_mul) ?_
  refine aqgd_dec_x (X := fun _ _ => True) (Q := fun _ _ => False) _ _ _ ?_
  refine aqgd_dec_x (X := fun _ _ => True) (Q := fun _ _ => False) _ _ _ ?_
  refine aqgd_dec_x (X := fun _ _ => True) (Q := fun _ _ => False) _ _ _ ?_
  refine aqgd_decCall_x (X := fun _ _ => True) (Q := fun _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_u256IsZero_lookup mf_u256_is_zero nb_u256_is_zero nc_u256_is_zero ?_
  refine aqgd_seq (aqgd_while_x (X := fun _ _ => True) _ ?_) (aqgd_seq (aqgd_callAssign_div hA hU hw _ _)
    (aqgd_return _ (fun _ _ _ _ _ _ _ _ => trivial)))
  exact tyLoop_aqgd hA hU hw

#print axioms taylor_window
end ty
end InitECandidate.Runtime
