import InitECandidate.Runtime.WitnessTraversalClockControl
import InitECandidate.Runtime.WitnessTraversalStateMeasureProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The actual data invariant paired with the actual state-derived rank. -/
def WitnessTraversalRank {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  WitnessTraversalInvariant layout s ∧ witnessTraversalStateMeasure layout.frame s=rank

def witnessTraversalCondition : ExpHOL 64 :=
  .cmp .notEqual (.var .local (ofString "go")) (.const 0)

theorem WitnessTraversalRank.after_clock {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (rank clock : Nat) (valid : WitnessTraversalRank layout s rank) :
    WitnessTraversalRank layout {s with clock:=clock} rank := by
  obtain ⟨⟨scratch,heap,top,mode,go,state⟩,ranked⟩ := valid
  exact ⟨⟨scratch,heap,top,mode,go,state.after_clock layout s scratch heap top mode go clock⟩,ranked⟩

theorem WitnessTraversalRank.zero_exit {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (valid : WitnessTraversalRank layout s 0) (word : BitVec 64)
    (condition : evalHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) witnessTraversalCondition=
      some (.val (.word word))) : word=0 := by
  obtain ⟨⟨scratch,heap,top,mode,go,state⟩,ranked⟩ := valid
  rcases state.goBits with stopped | running
  · have atGo := state.atGo
    rw [stopped] at atGo
    have evaluated : evalHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) witnessTraversalCondition=
        some (.val (.word (0#64))) := by
      simp [witnessTraversalCondition,evalHOLFinite,evalHOLExact,atGo,Compiler.Encoders.Asm.wordCmpHOL]
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (condition.symm.trans evaluated)))
  · have atGo := state.atGo
    rw [running] at atGo
    have positive := witnessTraversalStateMeasure_positive s layout.frame atGo
    omega
#print axioms WitnessTraversalRank.after_clock
#print axioms WitnessTraversalRank.zero_exit

/-- A nonzero actual loop condition selects the running go bit. -/
theorem WitnessTraversalState.running_of_condition {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go word : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go)
    (condition : evalHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) witnessTraversalCondition=
      some (.val (.word word))) (nonzero : word≠0) : go=1 := by
  rcases valid.goBits with stopped | running
  · have atGo := valid.atGo
    rw [stopped] at atGo
    have evaluated : evalHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) witnessTraversalCondition=
        some (.val (.word (0#64))) := by
      simp [witnessTraversalCondition,evalHOLFinite,evalHOLExact,atGo,Compiler.Encoders.Asm.wordCmpHOL]
    have zero := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (condition.symm.trans evaluated)))
    exact False.elim (nonzero zero)
  · exact running
#print axioms WitnessTraversalState.running_of_condition
end InitECandidate.Runtime
