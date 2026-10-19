import InitECandidate.Runtime.ResolveStepLookupBound
import InitECandidate.Runtime.DecodeStepExtensionUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem resolve_step_length_guard_bounded (condition : ExpHOL 64) :
    ProgBounded (.ite condition (.call (some (none,none)) (ofString "mpt_fail") [.const 10]) .skip) 1 := by
  apply ProgBounded.ite
  · intro F s code budget
    have bounded := evaluate_mptFail_call_bounded s (.const 10) 10 code (by omega) (by rfl)
    exact ⟨by rw [bounded.1]; omega,by rw [bounded.1]; omega,bounded.2.1⟩
  · exact ProgBounded.weaken (ProgBounded.straight .skip rfl) (by omega)

theorem runBounded_resolve_step_string {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total kind key payload consumed : BitVec 64) (built : NodedbTableAt s table heap total)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (budget : nodedbGetCost + 6 ≤ s.clock) :
    RunBounded s resolveStepStringBranch (nodedbGetCost + 6) := by
  by_cases empty : payload = 0
  · subst payload
    unfold RunBounded
    rw [source_resolve_step_string,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,
      evalListHOLExact,shapeOfHOLExact,emptyLocalsHOLFinite]
  · have guard : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0))
          (.return (.rstruct [.const 0,.const 0,.const 0,.const 0])) .skip) = (none,s) := by
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,
        show payload ≠ 0#64 from empty,evaluateHOLFiniteState_skip]
    rw [source_resolve_step_string]
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780,guard]
    change RunBounded s (.seq (.ite _ _ _) resolveStepLookup) (nodedbGetCost + 6)
    have bounded := RunBounded.seq (b := nodedbGetCost+5)
      (RunBounded.ofProg (resolve_step_length_guard_bounded (.cmp .notEqual (.rfield 2 (.var .local (ofString "it"))) (.const 32))) code (by omega)) (by omega : 1+(nodedbGetCost+5) ≤ s.clock)
      (by
        intro next normal nextCode ticks
        have same := mpt_fail_guard_normal_state s next _ 10 code normal
        subst next
        exact runBounded_resolve_step_lookup s table heap total kind key payload consumed built code atTable atItem ticks)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bounded

theorem runBounded_resolve_step_kind {F : Type} (s : PanSemStateFiniteExact 64 F)
    (table heap total kind key payload consumed : BitVec 64) (built : NodedbTableAt s table heap total)
    (code : s.code = originalRuntimeCode)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atItem : s.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word key),.val (.word payload),.val (.word consumed)]))
    (budget : nodedbGetCost + 6 ≤ s.clock) :
    RunBounded s (resolveStepAt 3) (nodedbGetCost + 6) := by
  have branch : RunBounded s
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0)) resolveStepStringBranch .skip)
      (nodedbGetCost + 6) := by
    unfold RunBounded
    rw [evaluateHOLFiniteState_ite]
    simp only [evalHOLExact,atItem]
    change (let flag := if kind = 0 then (1#64) else 0; _)
    by_cases zero : kind = 0
    · simp only [zero,if_pos,show (1#64) ≠ 0 from by decide,if_false]
      exact runBounded_resolve_step_string s table heap total kind key payload consumed built code atTable atItem budget
    · simp [Compiler.Encoders.Asm.wordCmpHOL,show kind ≠ 0#64 from zero,evaluateHOLFiniteState_skip]
  rw [source_resolve_step_kind]
  exact RunBounded.seq (b := 0) branch (by omega) (by
    intro next normal nextCode ticks
    exact RunBounded.ofProg (ProgBounded.straight _ rfl) (nextCode.trans code) ticks)

#print axioms resolve_step_length_guard_bounded
#print axioms runBounded_resolve_step_string
#print axioms runBounded_resolve_step_kind
end InitECandidate.Runtime
