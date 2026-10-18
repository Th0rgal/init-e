import InitECandidate.Runtime.CountedLoop
import InitECandidate.Runtime.MemeqConstCallBound
import InitECandidate.Runtime.TrapPrimitiveClock
import InitECandidate.Runtime.TrapNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ProgBounded.sharedStore (operator : OpSize) (address value : ExpHOL 64) :
    ProgBounded (.shMemStore operator address value) 0 := by
  intro F state _ _
  have clock := evaluate_shared_store_clock state operator address value
  exact ⟨by omega,by omega,evaluate_shared_store_no_timeout state operator address value⟩

theorem ProgBounded.iteMax (condition : ExpHOL 64) {yes no : ProgHOL 64} {a b : Nat}
    (left : ProgBounded yes a) (right : ProgBounded no b) : ProgBounded (.ite condition yes no) (max a b) :=
  ProgBounded.ite condition (left.weaken (Nat.le_max_left a b)) (right.weaken (Nat.le_max_right a b))

#print axioms ProgBounded.sharedStore
#print axioms ProgBounded.iteMax
end InitECandidate.Runtime
