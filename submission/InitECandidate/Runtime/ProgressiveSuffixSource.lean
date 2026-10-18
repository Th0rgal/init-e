import InitECandidate.Runtime.ProgressiveMerkleSource
import InitECandidate.Runtime.CountdownLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def progressiveFoldTail : ProgHOL 64 :=
  .call (some (none,none)) (ofString "sha256_pair")
    [.op .add [.var .local (ofString "roots"),.panop .mul [.var .local (ofString "k"),.const 32]],
      .var .local (ofString "acc"),.var .local (ofString "acc")]

def progressiveFoldLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "k")) (.const 0))
    (.seq (countdownAssign (ofString "k")) progressiveFoldTail)

theorem source_progressive_zero : progressiveAt 7 =
    .seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "acc"),.const 32])
      (progressiveAt 8) := by rfl

theorem source_progressive_fold : progressiveAt 8 = .seq progressiveFoldLoop (progressiveAt 9) := by rfl

theorem source_progressive_finish : progressiveAt 9 =
    .seq (.call (some (none,none)) (ofString "memcpy")
      [.var .local (ofString "out"),.var .local (ofString "acc"),.const 32])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
        (.return (.const 0))) := by rfl

#print axioms source_progressive_zero
#print axioms source_progressive_fold
#print axioms source_progressive_finish
end InitECandidate.Runtime
