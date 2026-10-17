import InitECandidate.Runtime.MptInsertFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Remaining key length, with one final iteration, when insertion is running. -/
def mptInsertLoopRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "go"),state.locals.lookup (ofString "level") with
  | some (.val (.word go)),some (.val (.word level)) => if go = 0 then 0 else length.toNat - level.toNat + 1
  | _,_ => 0

theorem eval_mptInsert_rank_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (go level length : BitVec 64)
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level))) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) =
      some (.val (.word (if mptInsertLoopRank length state = 0 then 0 else (1 : BitVec 64)))) := by
  by_cases zero : go = 0 <;>
    simp [mptInsertLoopRank,goLocal,levelLocal,zero,evalHOLFinite,evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL]

theorem mptInsertLoopRank_le {F : Type} (state : PanSemStateFiniteExact 64 F)
    (go level length : BitVec 64)
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (small : length.toNat ≤ 64) : mptInsertLoopRank length state ≤ 65 := by
  simp only [mptInsertLoopRank,goLocal,levelLocal]
  split <;> omega

/-- A stopped next iteration has rank zero; a running one decreases rank
whenever its actual key level strictly advances within the original length. -/
theorem mptInsertLoopRank_decreases {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (go nextGo level nextLevel length : BitVec 64)
    (goLocal : state.locals.lookup (ofString "go") = some (.val (.word go)))
    (nextGoLocal : post.locals.lookup (ofString "go") = some (.val (.word nextGo)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (nextLevelLocal : post.locals.lookup (ofString "level") = some (.val (.word nextLevel)))
    (running : go ≠ 0)
    (progress : nextGo ≠ 0 → level.toNat < nextLevel.toNat ∧ nextLevel.toNat ≤ length.toNat) :
    mptInsertLoopRank length post < mptInsertLoopRank length state := by
  simp only [mptInsertLoopRank,goLocal,nextGoLocal,levelLocal,nextLevelLocal,if_neg running]
  by_cases stopped : nextGo = 0
  · rw [if_pos stopped]
    omega
  · rw [if_neg stopped]
    obtain ⟨advanced,bounded⟩ := progress stopped
    omega

#print axioms eval_mptInsert_rank_guard
#print axioms mptInsertLoopRank_le
#print axioms mptInsertLoopRank_decreases
end InitECandidate.Runtime
