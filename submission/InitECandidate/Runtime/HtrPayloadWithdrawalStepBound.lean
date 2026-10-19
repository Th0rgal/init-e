import InitECandidate.Runtime.HtrPayloadSource
import InitECandidate.Runtime.HtrWithdrawalCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadWithdrawalArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "wd"),.panop .mul [.var .local (ofString "i"),.const 44]],
    .op .add [.var .local (ofString "roots"),.panop .mul [.var .local (ofString "i"),.const 32]]]

def htrPayloadWithdrawalStep : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "htr_withdrawal") htrPayloadWithdrawalArguments)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))

def htrPayloadWithdrawalCondition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))

theorem source_htrPayload_withdrawals : htrPayloadAt 28 =
    .seq (.while htrPayloadWithdrawalCondition htrPayloadWithdrawalStep) (htrPayloadAt 29) := by rfl

theorem htrPayload_withdrawal_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index roots : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrPayloadWithdrawalArguments =
      some [.val (.word (array + index * (44#64))),.val (.word (roots + index * (32#64)))] := by
  simp [htrPayloadWithdrawalArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,rootsLocal,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL]

theorem runBounded_htrPayload_withdrawal_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index roots heap : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "wd") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (rootsLocal : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrWithdrawalBodyCost + 1 ≤ state.clock) :
    RunBounded state htrPayloadWithdrawalStep (htrWithdrawalBodyCost + 1) := by
  have called := runBounded_htrWithdrawal_call state none htrPayloadWithdrawalArguments
    (array + index * (44#64)) (roots + index * (32#64)) heap
    (htrPayload_withdrawal_arguments state array index roots arrayLocal indexLocal rootsLocal)
    heapGlobal heapBound code budget
  have combined := RunBounded.seq
    (tail := .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (b := 0)
    called (by simpa using budget) (by
      intro next normal nextCode remaining
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans code) remaining)
  simpa [htrPayloadWithdrawalStep] using combined

#print axioms source_htrPayload_withdrawals
#print axioms htrPayload_withdrawal_arguments
#print axioms runBounded_htrPayload_withdrawal_step
end InitECandidate.Runtime
