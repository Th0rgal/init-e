import InitECandidate.Runtime.RecordHashBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrDepositBodyCost : Nat := 1 + (2 + recordHashCost depositHashSteps)

theorem runBounded_htrDeposit_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (e out heap : BitVec 64)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word e)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrDepositBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_deposit) htrDepositBodyCost := by
  rw [sourceFunctionBody_eq_structural,source_htrDeposit_record]
  exact recordHash_body_bound state (5#64) e out heap depositHashSteps atInput atOut hh cap
    (by simp [depositHashSteps,RecordHashStep.Small]) (by decide) code budget

#print axioms runBounded_htrDeposit_body

def htrWdreqBodyCost : Nat := 1 + (2 + recordHashCost wdreqHashSteps)

theorem runBounded_htrWdreq_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (e out heap : BitVec 64)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word e)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrWdreqBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_wdreq) htrWdreqBodyCost := by
  rw [sourceFunctionBody_eq_structural,source_htrWdreq_record]
  exact recordHash_body_bound state (3#64) e out heap wdreqHashSteps atInput atOut hh cap
    (by simp [wdreqHashSteps,RecordHashStep.Small]) (by decide) code budget

#print axioms runBounded_htrWdreq_body

def htrConsBodyCost : Nat := 1 + (2 + recordHashCost consHashSteps)

theorem runBounded_htrCons_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (e out heap : BitVec 64)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word e)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrConsBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_cons) htrConsBodyCost := by
  rw [sourceFunctionBody_eq_structural,source_htrCons_record]
  exact recordHash_body_bound state (3#64) e out heap consHashSteps atInput atOut hh cap
    (by simp [consHashSteps,RecordHashStep.Small]) (by decide) code budget

#print axioms runBounded_htrCons_body

def htrBdepBodyCost : Nat := 1 + (2 + recordHashCost bdepHashSteps)

theorem runBounded_htrBdep_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (e out heap : BitVec 64)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word e)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrBdepBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_bdep) htrBdepBodyCost := by
  rw [sourceFunctionBody_eq_structural,source_htrBdep_record]
  exact recordHash_body_bound state (4#64) e out heap bdepHashSteps atInput atOut hh cap
    (by simp [bdepHashSteps,RecordHashStep.Small]) (by decide) code budget

#print axioms runBounded_htrBdep_body

def htrBexitBodyCost : Nat := 1 + (2 + recordHashCost bexitHashSteps)

theorem runBounded_htrBexit_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (e out heap : BitVec 64)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word e)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cap : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrBexitBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_bexit) htrBexitBodyCost := by
  rw [sourceFunctionBody_eq_structural,source_htrBexit_record]
  exact recordHash_body_bound state (2#64) e out heap bexitHashSteps atInput atOut hh cap
    (by simp [bexitHashSteps,RecordHashStep.Small]) (by decide) code budget

#print axioms runBounded_htrBexit_body

end InitECandidate.Runtime
