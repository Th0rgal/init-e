import InitECandidate.Runtime.RunAttemptStateInitArguments
import InitECandidate.Runtime.RunAttemptStateInitLookup
import InitECandidate.Runtime.NodedbWholeBodyReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The two database calls' exact locals and protected-memory facts supply the
actual initializer arguments, including the old parent header state-root field.
No initializer runtime contract is assumed. -/
theorem run_attempt_state_init_after_database_frames {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (heap intermediateHeap parent stateRoot statePad pad output : BitVec 64)
    (ceiling : Nat)
    (locals : post.locals = (s.locals.update (ofString "nodedb",.val (.word heap))).update
      (ofString "codedb",.val (.word intermediateHeap)))
    (domain : post.memaddrs = s.memaddrs)
    (code : post.code = originalRuntimeCode)
    (frame : ∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w →
      ¬ MWin pad 136 w → ¬ MWin output 32 w → post.memory w = s.memory w)
    (atParent : s.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (parentDomain : s.memaddrs (parent + (32#64)))
    (parentCell : s.memory (parent + (32#64)) = .word stateRoot)
    (parentAbove : ceiling ≤ parent.toNat) (parentBefore : parent.toNat + 32 < heap.toNat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling) :
    evalListHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
      runAttemptStateInitArguments =
        some [.val (.word heap),.val (.word stateRoot),.val (.word intermediateHeap)] ∧
    lookupCodeHOLFinite post.code.lookup (ofString "state_init")
      [.val (.word heap),.val (.word stateRoot),.val (.word intermediateHeap)] =
      some (sourceFunctionBody Guest.guestFn_state_init,stateInitCallee heap stateRoot intermediateHeap,.one) := by
  have nodes : post.locals.lookup (ofString "nodedb") = some (.val (.word heap)) := by
    rw [locals]
    simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  have codes : post.locals.lookup (ofString "codedb") = some (.val (.word intermediateHeap)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have parentLocal : post.locals.lookup (ofString "parent") = some (.val (.word parent)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atParent
  have address : (parent + (32#64)).toNat = parent.toNat + 32 := by
    have top := heap.isLt
    have small : (32#64).toNat = 32 := rfl
    rw [BitVec.toNat_add_of_lt (by omega)]
    rfl
  have kept : post.memory (parent + (32#64)) = s.memory (parent + (32#64)) := by
    apply frame _ (by rw [address]; omega)
    all_goals apply mwin_below; rw [address]; omega
  refine ⟨eval_run_attempt_state_init_arguments post heap parent stateRoot intermediateHeap nodes parentLocal codes
    (by rw [domain]; exact parentDomain) (kept.trans parentCell),?_⟩
  rw [code]
  exact lookup_state_init_callee heap stateRoot intermediateHeap

#print axioms run_attempt_state_init_after_database_frames
end InitECandidate.Runtime
