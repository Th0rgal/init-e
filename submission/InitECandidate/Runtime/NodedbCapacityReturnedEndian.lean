import InitECandidate.Runtime.NodedbCapacityPrefixEndian
import InitECandidate.Runtime.ReachesReturnedContinuation
import InitECandidate.Runtime.NodedbBodyBound
/-!
The capacity prefix of the real `nodedb_build` body, seen from a returned run.

`nodedb_capacity_prefix_endian_reaches` already carries the whole capacity frame in its
reach predicate: the guessed capacity is typed, big enough and a power of two,
and the prefix leaves memory, globals, the instruction code, the mapped
addresses and every local except `cap` exactly as they were.  Composing it with
`reaches_returned_continuation` on an actual returned body run exposes the real
`At 2` state together with the retained `At 2` execution: the constructor/loop
tail runs from that state, returns the same value, and its final memory,
globals and mapped addresses are the ones of the whole-body run.  No callee
contract and no post-prefix preservation is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- A returned run of the actual node-database body exposes its capacity `At 2`
state: the prefix predicate holds there, the prefix cost is charged, and the
retained `At 2` tail returns the same value with the body run's final memory,
globals and mapped addresses. -/
theorem nodedb_body_capacity_returned_endian_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (count : BitVec 64) (value : ValueHOL 64)
    (code : s.code = originalRuntimeCode)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 134217712) (budget : 2 * count.toNat + 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build) =
      (some (.returned value),post)) :
    ∃ ready at2post : PanSemStateFiniteExact 64 F,
      (∃ capacity : BitVec 64, ready.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
        2 * count.toNat + 2 ≤ capacity.toNat ∧ capacity.toNat ≤ 536870912 ∧
        (∃ bits : Nat, 2 ≤ bits ∧ capacity.toNat = 2 ^ bits)) ∧
      ready.memory = s.memory ∧ ready.globals = s.globals ∧ ready.code = s.code ∧
      ready.memaddrs = s.memaddrs ∧ ready.be = s.be ∧
      (∀ key : MlS, key ≠ ofString "cap" → ready.locals.lookup key = s.locals.lookup key) ∧
      s.clock ≤ ready.clock + (2 * count.toNat + 2) ∧ ready.clock ≤ s.clock ∧
      evaluateHOLFiniteState ready (nodedbAt 2) = (some (.returned value),at2post) ∧
      at2post.clock = post.clock ∧ at2post.memory = post.memory ∧
      at2post.globals = post.globals ∧ at2post.memaddrs = post.memaddrs := by
  have returned : (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build)).1 =
      some (.returned value) := by rw [run]
  have bodyPair : evaluateHOLFiniteState s (nodedbAt 0) = (some (.returned value),post) := by
    rw [← source_nodedb_body]; exact run
  rw [source_nodedb_body] at returned
  have reached := nodedb_capacity_prefix_endian_reaches s count code atCount small budget
  obtain ⟨ready,valid,spent,remaining,scopeEq,normal⟩ :=
    reaches_returned_continuation s (nodedbAt 0) (nodedbAt 2) _ (2 * count.toNat + 2) value reached
      returned
  obtain ⟨capacity,capLocal,capacityLower,capacityUpper,power⟩ := valid.1
  have clockEq := scopeEq.2.1
  have memoryEq := scopeEq.2.2.1
  have globalsEq := scopeEq.2.2.2.1
  have domainEq := scopeEq.2.2.2.2
  rw [bodyPair] at clockEq memoryEq globalsEq domainEq
  refine ⟨ready,(evaluateHOLFiniteState ready (nodedbAt 2)).2,⟨capacity,capLocal,capacityLower,
    capacityUpper,power⟩,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,valid.2.2.2.2.2.1,valid.2.2.2.2.2.2,
    spent,remaining,Prod.ext normal rfl,clockEq.symm,memoryEq.symm,globalsEq.symm,domainEq.symm⟩

#print axioms nodedb_body_capacity_returned_endian_frame
end InitECandidate.Runtime
