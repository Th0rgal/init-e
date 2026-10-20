import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.PanPropsEvalStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem evalHOLFinite_memaddrs_mono {width : Nat} {F : Type} [NeZero width]
    (s : PanSemStateFiniteExact width F) (domain : BitVec width→Prop)
    (subset : ∀ address, s.memaddrs address→domain address) (expression : ExpHOL width) (value : ValueHOL width)
    (run : @evalHOLFinite width F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some value) :
    @evalHOLFinite width F _ {s with memaddrs:=domain} (fun a=>Classical.propDecidable (domain a)) expression=some value := by
  classical
  have output := evalSwapMemaddrsHOLFinite (PanPropsEvalStateFiniteExact.ofPanSemFinite s) expression value domain ⟨run,subset⟩
  exact output
 theorem evalListHOLFinite_memaddrs_mono {width : Nat} {F : Type} [NeZero width]
    (s : PanSemStateFiniteExact width F) (domain : BitVec width→Prop)
    (subset : ∀ address, s.memaddrs address→domain address) (expressions : List (ExpHOL width)) (values : List (ValueHOL width))
    (run : @evalListHOLFinite width F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expressions=some values) :
    @evalListHOLFinite width F _ {s with memaddrs:=domain} (fun a=>Classical.propDecidable (domain a)) expressions=some values := by
  classical
  induction expressions generalizing values with
  | nil => simpa [evalListHOLFinite,evalListHOLExact] using run
  | cons expression expressions ih =>
    simp only [evalListHOLFinite,evalListHOLExact] at run ⊢
    cases first : @evalHOLFinite width F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
    | none => simp [evalHOLFinite_eq_toExact] at first; simp [first] at run
    | some value =>
      have firstNext := evalHOLFinite_memaddrs_mono s domain subset expression value first
      cases rest : @evalListHOLFinite width F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) expressions with
      | none => simp [evalListHOLFinite] at rest; simp [evalHOLFinite_eq_toExact,first,rest] at run
      | some vals =>
        have restNext := ih vals rest
        simp only [evalHOLFinite_eq_toExact] at first firstNext
        simp only [evalListHOLFinite] at rest restNext
        simpa only [first,rest,firstNext,restNext] using run
#print axioms evalListHOLFinite_memaddrs_mono
#print axioms evalHOLFinite_memaddrs_mono
end InitECandidate.Runtime
