import InitECandidate.Runtime.WitnessScratchChain
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- Keeping the current saved link and every older record interval suffices;
updates to other fields inside the current88-byte record remain permitted. -/
theorem WitnessScratchChain.after_head_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top : BitVec 64) (upper lower nextLower : Nat) (chain : WitnessScratchChain s upper lower top)
    (lowerMoves : nextLower≤lower)
    (headFrame : post.memory top=s.memory top)
    (olderFrame : ∀ watched : BitVec 64, top.toNat+88≤watched.toNat → watched.toNat<upper → post.memory watched=s.memory watched) :
    WitnessScratchChain post upper nextLower top := by
  cases chain with
  | nil => exact .nil
  | cons above positive before link ordered tail =>
    refine .cons (by omega) positive before (headFrame.trans link) ordered ?_
    have older := tail.rebase s _ upper lower (top.toNat+88) ordered
    exact older.after_frame s post _ upper (top.toNat+88) nextLower (by omega) olderFrame

theorem WitnessScratchChain.head_bounds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (top : BitVec 64) (upper lower : Nat) (chain : WitnessScratchChain s upper lower top) (nonempty : top≠0) :
    lower≤top.toNat ∧ 0<top.toNat ∧ top.toNat+88≤upper := by
  cases chain with
  | nil => exact False.elim (nonempty rfl)
  | cons above positive before link ordered tail => exact ⟨above,positive,before⟩
#print axioms WitnessScratchChain.after_head_frame
#print axioms WitnessScratchChain.head_bounds
end InitECandidate.Runtime
