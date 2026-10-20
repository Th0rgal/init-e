import InitECandidate.Runtime.PanStoreChain
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- Actual word or structure stores reach their continuation without clock
cost, preserving caller bindings, globals, code and domain, or reject. -/
theorem StoreChain.reaches {program tail : ProgHOL 64} (chain : StoreChain program tail)
 {F : Type} (s : PanSemStateFiniteExact 64 F) :
 Reaches s program (fun next=>next.locals=s.locals ∧ next.globals=s.globals ∧
 next.code=s.code ∧ next.memaddrs=s.memaddrs) 0 tail := by
 induction chain generalizing s with
 | nil => exact Or.inl ⟨s,⟨rfl,rfl,rfl,rfl⟩,by omega,le_refl _,scoped_refl _⟩
 | @cons destination value restProgram tailProgram rest ih =>
   have control:=evaluate_store_control_frame s destination value
   have globals : (evaluateHOLFiniteState s (.store destination value)).2.globals=s.globals := by
    rw [evaluateHOLFiniteState_store]
    repeat' first | split | rfl
   have metadata:=evaluateHOLFiniteState_metadata s (.store destination value)
   have firstRun : Reaches s (.seq (.store destination value) restProgram) (fun next=>next.locals=s.locals ∧
    next.globals=s.globals ∧next.code=s.code ∧next.memaddrs=s.memaddrs) 0 restProgram := by
    apply reaches_seq
    cases run : evaluateHOLFiniteState s (.store destination value) with
    | mk result next =>
      rw [run] at control globals metadata
      have clockEq : next.clock=s.clock := control.2.2
      rcases control.1 with normal | failed
      · dsimp only at normal
        subst result
        exact Or.inl ⟨next,⟨control.2.1,globals,metadata.1,metadata.2.1⟩,by omega,by omega,rfl⟩
      · dsimp only at failed
        subst result
        right
        exact ⟨.error,rfl,by simp,by dsimp only;omega,by dsimp only;omega,fun _=>by simp⟩
   exact reaches_trans s _ restProgram tailProgram _ _ 0 0 firstRun (fun next facts=>
    reaches_mono next restProgram tailProgram _ _ 0 0 (le_refl _) (fun final kept=>
     ⟨kept.1.trans facts.1,kept.2.1.trans facts.2.1,kept.2.2.1.trans facts.2.2.1,
      kept.2.2.2.trans facts.2.2.2⟩) (ih next))
#print axioms StoreChain.reaches
end InitECandidate.Runtime
