import InitECandidate.Runtime.MainInputSource
import InitECandidate.Runtime.MemzeroAlignedCall
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Main's actual zeroing call and two local declarations reach the handled
decoder call in at most 33 source ticks. Scope restoration is explicit. -/
theorem evaluate_main_zero_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (zero : BitVec 64)
    (atZero : state.locals.lookup (ofString "z32") = some (.val (.word zero)))
    (code : state.code = originalRuntimeCode) (budget : 33 ≤ state.clock)
    (small : zero.toNat + 32 ≤ 33806089496) (aligned : zero.toNat % 8 = 0)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (zero + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (zero + BitVec.ofNat 64 offset))) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      Scoped (evaluateHOLFiniteState state (mainAt 17)) (evaluateHOLFiniteState ready (mainAt 20)) ∧
      state.clock ≤ ready.clock + 33 ∧ ready.clock ≤ state.clock ∧
      ZeroBytePrefix ready zero 32 ∧
      ready.locals = (state.locals.update (ofString "si",.val (.word 0))).update (ofString "err_code",.val (.word 0)) ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "z32"),.const 32] = some [.val (.word zero),.val (.word 32)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atZero]
  obtain ⟨cleared,run,covered,cost,remaining,globals,installed,domain,_,locals,_⟩ :=
    evaluate_memzero_aligned_call state (.var .local (ofString "z32")) (.const 32) zero 32 args code budget
      small aligned wordDomain byteDomain
  let ready := setVarHOLFinite (ofString "err_code") (.val (.word 0))
    (setVarHOLFinite (ofString "si") (.val (.word 0)) cleared)
  have agreement : Scoped (evaluateHOLFiniteState cleared (mainAt 18)) (evaluateHOLFiniteState ready (mainAt 20)) := by
    rw [source_main_si_declaration,source_main_error_declaration]
    simp only [evaluateHOLFiniteState_dec_total,evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨ready,?_,cost,remaining,covered,?_,globals,installed,domain⟩
  · rw [source_main_zero_call,evaluateHOLFiniteState_seq_line780,run]
    exact agreement
  · change (cleared.locals.update _).update _ = _
    rw [locals]

#print axioms evaluate_main_zero_prefix
end InitECandidate.Runtime
