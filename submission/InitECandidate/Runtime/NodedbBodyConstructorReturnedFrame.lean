import InitECandidate.Runtime.NodedbCapacityReturnedFrame
import InitECandidate.Runtime.NodedbConstructorReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- A returned original builder run reaches its real insertion suffix with
the constructor invariant and enough clock for the entire insertion loop.
The capacity and constructor frames are derived from their actual runs. -/
theorem nodedb_body_constructor_returned_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) (total pointer : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (small : total.toNat ≤ 134217712)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (budget : nodedbBodyCost total ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build) =
      (some (.returned value),post)) :
    ∃ capacity : BitVec 64, ∃ bits : Nat, ∃ at2 next tailPost : PanSemStateFiniteExact 64 F,
      2 * total.toNat + 2 ≤ capacity.toNat ∧ capacity.toNat ≤ 536870912 ∧
      2 ≤ bits ∧ capacity.toNat = 2^bits ∧
      at2.memory = s.memory ∧ at2.globals = s.globals ∧ at2.code = s.code ∧ at2.memaddrs = s.memaddrs ∧
      (∀ key : MlS, key ≠ ofString "cap" → at2.locals.lookup key = s.locals.lookup key) ∧
      NodedbTableReady at2 pointer capacity bits next ∧
      total.toNat * (nodedbIterationCost capacity total + 1) ≤ next.clock ∧
      evaluateHOLFiniteState next (nodedbAt 3) = (some (.returned value),tailPost) ∧
      tailPost.clock = post.clock ∧ tailPost.memory = post.memory ∧
      tailPost.globals = post.globals ∧ tailPost.memaddrs = post.memaddrs := by
  obtain ⟨at2,at2Post,⟨capacity,atCap,margin,capacitySmall,bits,bitsLower,power⟩,
    memory,globals,installed,domain,locals,spent,remaining,tailRun,clockEq,memoryEq,globalsEq,domainEq⟩ :=
    nodedb_body_capacity_returned_frame s post total value code atTotal small
      (by unfold nodedbBodyCost at budget; omega) run
  have afterPrefix : nodedbTailCost total ≤ at2.clock := by
    unfold nodedbBodyCost at budget
    omega
  have constructorCost := nodedb_constructor_cost_le capacity total capacitySmall
  obtain ⟨next,tailPost,ready,constructorSpent,constructorRemaining,returned,
    finalClock,finalMemory,finalGlobals,finalDomain⟩ :=
    nodedb_constructor_returned_frame at2 at2Post pointer capacity bits (installed.trans code) atCap
      (by rw [globals]; exact atHeap) aligned capped
      (by intro a al lo hi; rw [domain]; exact arena a al lo hi) power
      (by omega) value tailRun
  exact ⟨capacity,bits,at2,next,tailPost,margin,capacitySmall,bitsLower,power,memory,globals,installed,domain,locals,
    ready,by omega,returned,finalClock.trans clockEq,finalMemory.trans memoryEq,
    finalGlobals.trans globalsEq,finalDomain.trans domainEq⟩

#print axioms nodedb_body_constructor_returned_frame
end InitECandidate.Runtime
