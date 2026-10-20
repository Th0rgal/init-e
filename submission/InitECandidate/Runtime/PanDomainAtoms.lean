import InitECandidate.Runtime.PanDomainBytearray
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 def PanDomainMonoAt {F : Type} (program : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ domain : BitVec 64→Prop, (∀ address,s.memaddrs address→domain address)→
    (evaluateHOLFiniteState s program).1≠some .error→
    evaluateHOLFiniteState {s with memaddrs:=domain} program=
      ((evaluateHOLFiniteState s program).1,{(evaluateHOLFiniteState s program).2 with memaddrs:=domain})
 theorem panDomainMono_skip {F : Type} (s : PanSemStateFiniteExact 64 F) : PanDomainMonoAt .skip s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_skip]
 theorem panDomainMono_break {F : Type} (s : PanSemStateFiniteExact 64 F) : PanDomainMonoAt .break s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_break]
 theorem panDomainMono_continue {F : Type} (s : PanSemStateFiniteExact 64 F) : PanDomainMonoAt .continue s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_continue]
 theorem panDomainMono_annot {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS) : PanDomainMonoAt (.annot a b) s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_annot]
 theorem panDomainMono_tick {F : Type} (s : PanSemStateFiniteExact 64 F) : PanDomainMonoAt .tick s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_tick]
  split <;> rfl
 theorem panDomainMono_return {F : Type} (s : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) : PanDomainMonoAt (.return expression) s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_return] at valid ⊢
  cases old : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
  | none => simp only [evalHOLFinite_eq_toExact] at old;simp only [old,ne_eq,not_true_eq_false] at valid
  | some value =>
    have next := evalHOLFinite_memaddrs_mono s domain subset expression value old
    simp only [evalHOLFinite_eq_toExact] at old next
    simp only [old] at valid ⊢
    simp only [next]
    split at valid
    · rename_i size
      simp only [size,if_pos,emptyLocalsHOLFinite]
    · simp_all
 theorem panDomainMono_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (kind : VarKind) (name : MlS) (expression : ExpHOL 64) : PanDomainMonoAt (.assign kind name expression) s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_assign] at valid ⊢
  cases old : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
  | none => simp only [evalHOLFinite_eq_toExact] at old;simp [old] at valid
  | some value =>
    have next := evalHOLFinite_memaddrs_mono s domain subset expression value old
    simp only [evalHOLFinite_eq_toExact] at old next
    simp only [old] at valid ⊢
    simp only [next]
    split at valid
    · rename_i allowed
      have eq : isValidValueHOLFinite {s with memaddrs:=domain} kind name value=isValidValueHOLFinite s kind name value := by cases kind <;>rfl
      simp only [eq,allowed,if_true]
      cases kind <;> rfl
    · simp_all
 theorem panDomainMono_raise {F : Type} (s : PanSemStateFiniteExact 64 F) (exception : MlS) (expression : ExpHOL 64) : PanDomainMonoAt (.raise exception expression) s := by
  classical
  intro domain subset valid
  have eshapes : ({s with memaddrs:=domain} : PanSemStateFiniteExact 64 F).eshapes=s.eshapes := rfl
  simp only [evaluateHOLFiniteState_raise,eshapes] at valid ⊢
  cases shapeRun : s.eshapes.lookup exception with
  | none => simp only [shapeRun] at valid;cases valid rfl
  | some shape =>
    cases old : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
    | none => simp only [evalHOLFinite_eq_toExact] at old;simp [shapeRun,old] at valid
    | some value =>
      have next := evalHOLFinite_memaddrs_mono s domain subset expression value old
      simp only [evalHOLFinite_eq_toExact] at old next
      simp only [shapeRun,old] at valid ⊢
      simp only [next]
      by_cases allowed : shapeOfHOLExact value=shape ∧ sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value)≤32
      · simp only [if_pos allowed,emptyLocalsHOLFinite]
      · simp only [if_neg allowed] at valid
        exact False.elim (valid rfl)
 theorem panDomainMono_primitive {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (operator : PrimOp) (expressions : List (ExpHOL 64)) : PanDomainMonoAt (.primitive name operator expressions) s := by
  intro domain subset valid
  simp only [evaluateHOLFiniteState_primitive] at valid ⊢
  cases old : @evalListHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expressions with
  | none => simp only [evalListHOLFinite] at old;simp [old] at valid
  | some values =>
    have next := evalListHOLFinite_memaddrs_mono s domain subset expressions values old
    simp only [evalListHOLFinite] at old next
    simp only [old] at valid ⊢
    simp only [next]
    cases result : panPrimopHOLExact operator values with
    | none => simp [result] at valid
    | some value =>
      simp only [result] at valid ⊢
      split at valid
      · rename_i allowed
        have eq : isValidValueHOLFinite {s with memaddrs:=domain} .local name value=isValidValueHOLFinite s .local name value := rfl
        simp only [eq,allowed,if_true]
        rfl
      · simp_all
#print axioms panDomainMono_assign
#print axioms panDomainMono_raise
#print axioms panDomainMono_primitive
#print axioms panDomainMono_skip
#print axioms panDomainMono_break
#print axioms panDomainMono_continue
#print axioms panDomainMono_annot
#print axioms panDomainMono_tick
#print axioms panDomainMono_return
end InitECandidate.Runtime
