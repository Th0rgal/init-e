import InitECandidate.Runtime.GlobalConstantStores
import InitECandidate.Runtime.GlobalAllocationPrefix
import InitECandidate.Runtime.OriginalBlake2InitCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def blake2SigmaCells : List (BitVec 64 × BitVec 64) := [(0,18364758544493064720),(8,3853709921291437230),(16,5266788149650328715),(24,10305543691612001175),(32,15242093322790139145),(40,10515720223929181890),(48,13270197634454188380),(56,11702690517083809725),(64,6503616966983130870),(72,991893350865389610)]
def blake2IvCells : List (BitVec 64 × BitVec 64) := [(0,7640891576956012808),(8,13503953896175478587),(16,4354685564936845355),(24,11912009170470909681),(32,5840696475078001361),(40,11170449401992604703),(48,2270897969802886507),(56,6620516959819538809)]

def blake2InitTail : ProgHOL 64 :=
  .seq (.assign .global (ofString "b2_v") (.op .add [.var .global (ofString "b2_round"),.const 8]))
  (.seq (.assign .global (ofString "b2_m") (.op .add [.var .global (ofString "b2_round"),.const 136]))
  (globalConstantStores (ofString "b2_sigma") blake2SigmaCells
    (globalConstantStores (ofString "b2_iv") blake2IvCells (.return (.const 0)))))

def blake2InitAllocations : List (MlS × BitVec 64) :=
  [(ofString "b2_sigma",80),(ofString "b2_iv",64),(ofString "b2_round",264)]

theorem source_blake2Init_body : sourceFunctionBody Guest.guestFn_blake2_init =
    .seq (.ite (.cmp .notEqual (.var .global (ofString "b2_sigma")) (.const 0)) (.return (.const 0)) .skip)
      (globalAllocationProgram blake2InitAllocations blake2InitTail) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_blake2Init_body
end InitECandidate.Runtime
