import InitECandidate.Runtime.HtrPayloadWithdrawalBlockBound
import InitECandidate.Runtime.HtrPayloadTxInitialization
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_htrPayload_withdrawal_allocation : htrPayloadAt 26 =
    .seq (.call (some (some (.local,ofString "roots"),none)) (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nwd"),.const 32],.const 32]]
      ) (htrPayloadAt 27) := by rfl

theorem source_htrPayload_withdrawal_zero : htrPayloadAt 27 =
    .seq (.assign .local (ofString "i") (.const 0)) (htrPayloadAt 28) := by rfl

theorem htrPayload_withdrawal_allocation_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count : BitVec 64)
    (countLocal : state.locals.lookup (ofString "nwd") = some (.val (.word count))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.op .add [.panop .mul [.var .local (ofString "nwd"),.const 32],.const 32]] =
      some [.val (.word (htrPayloadTxAllocationSize count))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,wordOpHOL,wordOp,
    panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,htrPayloadTxAllocationSize]

#print axioms source_htrPayload_withdrawal_allocation
#print axioms source_htrPayload_withdrawal_zero
#print axioms htrPayload_withdrawal_allocation_arguments
end InitECandidate.Runtime
