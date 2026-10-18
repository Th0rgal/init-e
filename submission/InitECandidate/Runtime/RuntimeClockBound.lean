import InitECandidate.Runtime.Bswap64CallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform bounds for source fragments using the original runtime code. -/
def RuntimeClockBound (program : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode → cost ≤ state.clock →
    let evaluated := evaluateHOLFiniteState state program
    state.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut

theorem runtimeClockBound_straight (program : ProgHOL 64) (supported : straightLine program = true) :
    RuntimeClockBound program 0 := by
  intro F state code budget
  have clock := clockPreserving_of_straightLine program supported state
  exact ⟨by omega,by omega,evaluate_straightLine_no_timeout program supported state⟩

theorem runtimeClockBound_prefix (first tail : ProgHOL 64) (cost : Nat)
    (supported : straightLine first = true) (bounded : RuntimeClockBound tail cost) :
    RuntimeClockBound (.seq first tail) cost := by
  intro F state code budget
  have clock := clockPreserving_of_straightLine first supported state
  have safe := evaluate_straightLine_no_timeout first supported state
  have metadata := (evaluateHOLFiniteState_metadata state first).1
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result post =>
    rw [run] at clock safe metadata
    dsimp only at clock safe metadata
    cases result with
    | none =>
      dsimp only
      have tailBound := bounded post (metadata.trans code) (by omega)
      exact ⟨by dsimp only at tailBound; omega,by dsimp only at tailBound; omega,tailBound.2.2⟩
    | some result => exact ⟨by dsimp only; omega,by dsimp only; omega,safe⟩

theorem runtimeClockBound_dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
    (body : ProgHOL 64) (cost : Nat) (bounded : RuntimeClockBound body cost) :
    RuntimeClockBound (.dec name shape initializer body) cost := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨by simp,by simp,by simp⟩
  · rename_i value initialized
    split
    · have bound := bounded (setVarHOLFinite name value state) code budget
      cases run : evaluateHOLFiniteState (setVarHOLFinite name value state) body with
      | mk result post =>
        rw [run] at bound
        exact bound
    · exact ⟨by simp,by simp,by simp⟩

theorem runtimeClockBound_bswap64 (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (body : ProgHOL 64) (cost : Nat) (bounded : RuntimeClockBound body cost) :
    RuntimeClockBound (.decCall name shape (ofString "bswap64") arguments body) (1 + cost) := by
  intro F state code budget
  exact evaluate_bswap64_call_bounded state name shape arguments body cost code
    (fun current installed enough => bounded current installed enough) budget

#print axioms runtimeClockBound_prefix
#print axioms runtimeClockBound_dec
#print axioms runtimeClockBound_bswap64
end InitECandidate.Runtime
