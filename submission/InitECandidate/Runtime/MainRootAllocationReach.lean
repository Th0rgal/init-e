import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.MainInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_main_root_declaration : mainAt 21 =
    .decCall (ofString "root") .one (ofString "alloc") [.const 32] (mainAt 22) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem main_root_allocation_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capped : pointer.toNat ≤ 33806089496) (budget : 2 ≤ state.clock) :
    Reaches state (mainAt 21) (AllocationDeclarationReady state (ofString "root") pointer 32) 2 (mainAt 22) := by
  rw [source_main_root_declaration]
  exact evaluate_allocation_declaration_reaches state (.const 32) (ofString "root") pointer 32
    (mainAt 22) rfl code heap capped budget

#print axioms source_main_root_declaration
#print axioms main_root_allocation_reaches
end InitECandidate.Runtime
