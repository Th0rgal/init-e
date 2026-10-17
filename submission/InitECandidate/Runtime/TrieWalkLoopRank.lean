import InitECandidate.Runtime.TrieWalkTraversalRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Null nodes terminate immediately, even when unconsumed key nibbles remain.
Non-null nodes retain the combined nibble/address rank plus one. -/
def trieWalkLoopRank {F : Type} (length : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "node") with
  | some (.val (.word node)) => if node = 0 then 0 else trieWalkTraversalRank length state + 1
  | _ => 0

/-- The rank's zero case agrees with the exact original while guard. -/
theorem eval_trieWalk_loop_rank_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node))) :
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "node")) (.const 0)) =
      some (.val (.word (if trieWalkLoopRank length state = 0 then 0 else (1 : BitVec 64)))) := by
  by_cases zero : node = 0 <;>
    simp [trieWalkLoopRank,nodeLocal,zero,evalHOLFinite,evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL]

/-- A uniform finite ceiling for the exact-guard rank on64-nibble keys. -/
theorem trieWalkLoopRank_le {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index node length : BitVec 64)
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (keySize : length.toNat ≤ 64) : trieWalkLoopRank length state ≤ 65 * 2^64 := by
  have ceiling := trieWalkTraversalRank_lt state index node length posLocal nodeLocal keySize
  simp only [trieWalkLoopRank,nodeLocal]
  split <;> omega

/-- A combined-rank decrease also decreases the guard-compatible rank;
a transition to the null node terminates regardless of remaining key length. -/
theorem trieWalkLoopRank_decreases {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (node child length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (childLocal : post.locals.lookup (ofString "node") = some (.val (.word child)))
    (nonzero : node ≠ 0)
    (decrease : trieWalkTraversalRank length post < trieWalkTraversalRank length state) :
    trieWalkLoopRank length post < trieWalkLoopRank length state := by
  simp only [trieWalkLoopRank,nodeLocal,childLocal,if_neg nonzero]
  split <;> omega

#print axioms eval_trieWalk_loop_rank_guard
#print axioms trieWalkLoopRank_le
#print axioms trieWalkLoopRank_decreases
end InitECandidate.Runtime
