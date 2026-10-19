import InitECandidate.Runtime.OriginalValidateHeadersCode
import InitECandidate.Runtime.StatelessAt22
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.TrapNoReturn
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def validateHeadersAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_validate_headers)
def validateHeadersCountCondition : ExpHOL 64 :=
  .cmp .lower (.const 256) (.var .local (ofString "n"))
def validateHeadersCountGuard : ProgHOL 64 :=
  .ite validateHeadersCountCondition (.raise (ofString "BlockErr") (.const 1)) .skip

theorem source_validate_headers_body : sourceFunctionBody Guest.guestFn_validate_headers = validateHeadersAt 0 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_validate_headers_guard : validateHeadersAt 0 =
    .seq validateHeadersCountGuard (validateHeadersAt 1) := rfl

theorem eval_validate_headers_count_condition {F : Type} (s : PanSemStateFiniteExact 64 F) (n : BitVec 64)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) validateHeadersCountCondition =
      some (.val (.word (if 256 < n.toNat then 1 else 0))) := by
  simp [evalHOLFinite_eq_toExact,validateHeadersCountCondition,evalHOLExact,evalListHOLExact,atCount,
    Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- An actual returned header-validation body passed the original unsigned
256-header guard. Oversized counts raise BlockErr before allocation. -/
theorem validate_headers_returned_count {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (v : ValueHOL 64)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_headers) = (some (.returned v),post)) :
    n.toNat ≤ 256 := by
  classical
  by_contra large
  have positive : 256 < n.toNat := by omega
  have cond := eval_validate_headers_count_condition s n atCount
  simp only [if_pos positive] at cond
  rw [source_validate_headers_body,source_validate_headers_guard,evaluateHOLFiniteState_seq_line780] at run
  have guard : evaluateHOLFiniteState s validateHeadersCountGuard =
      evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 1)) := by
    unfold validateHeadersCountGuard
    rw [evaluateHOLFiniteState_ite]
    rw [show evalHOLExact s.toExact validateHeadersCountCondition = some (.val (.word (1#64))) from cond]
    simp
  rw [guard] at run
  have noNormal : (evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 1))).1 ≠ none := by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split <;> simp
    · simp
  have noReturn := evaluate_raise_no_return s (ofString "BlockErr") (.const 1) v
  cases raised : evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 1)) with
  | mk result next =>
    rw [raised] at run noNormal noReturn
    cases result with
    | none => exact noNormal rfl
    | some r => exact noReturn (Prod.mk.inj run).1

#print axioms eval_validate_headers_count_condition
#print axioms validate_headers_returned_count
end InitECandidate.Runtime
