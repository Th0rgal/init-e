import InitECandidate.Runtime.GlobalAllocationZeroPrefix
import InitECandidate.Runtime.InitializerCounterSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def globalAllocationZeroProgram (name : MlS) (size : BitVec 64) (tail : ProgHOL 64) : ProgHOL 64 :=
  globalAllocationProgram [(name,size)]
    (.seq (.call (some (none,none)) (ofString "memzero") [.var .global name,.const size]) tail)

theorem source_forkInit_zero32 : forkInitAt 0 =
    globalAllocationZeroProgram (ofString "zero32") 32 (forkInitAt 2) := by
  simp only [forkInitAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_forkInit_precompile_allocation : forkInitAt 2 =
    .seq (.call (some (some (.global,ofString "precompile_addrs"),none)) (ofString "alloc")
      [.panop .mul [.const 18,.const 20]])
    (.seq (.call (some (none,none)) (ofString "memzero")
      [.var .global (ofString "precompile_addrs"),.panop .mul [.const 18,.const 20]]) (forkInitAt 4)) := by
  simp only [forkInitAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The literal product is normalized through expression evaluation, without
modifying the challenge AST. -/
theorem evaluate_forkInit_precompile_normalized {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (forkInitAt 2) = evaluateHOLFiniteState state
      (globalAllocationZeroProgram (ofString "precompile_addrs") 360 (forkInitAt 4)) := by
  have allocEq (current : PanSemStateFiniteExact 64 F) :
      evaluateHOLFiniteState current
        (.call (some (some (.global,ofString "precompile_addrs"),none)) (ofString "alloc")
          [.panop .mul [.const 18,.const 20]]) =
      evaluateHOLFiniteState current
        (.call (some (some (.global,ofString "precompile_addrs"),none)) (ofString "alloc") [.const 360]) := by
    have arguments : evalListHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
        [.panop .mul [.const 18,.const 20]] =
        evalListHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a)) [.const 360] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord]
    simp only [evaluateHOLFiniteState_call]
    rw [arguments]
  have zeroEq (current : PanSemStateFiniteExact 64 F) :
      evaluateHOLFiniteState current
        (.call (some (none,none)) (ofString "memzero")
          [.var .global (ofString "precompile_addrs"),.panop .mul [.const 18,.const 20]]) =
      evaluateHOLFiniteState current
        (.call (some (none,none)) (ofString "memzero")
          [.var .global (ofString "precompile_addrs"),.const 360]) := by
    have arguments : evalListHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
        [.var .global (ofString "precompile_addrs"),.panop .mul [.const 18,.const 20]] =
        evalListHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
          [.var .global (ofString "precompile_addrs"),.const 360] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord]
    simp only [evaluateHOLFiniteState_call]
    rw [arguments]
  rw [source_forkInit_precompile_allocation]
  simp only [globalAllocationZeroProgram,globalAllocationProgram,evaluateHOLFiniteState_seq_line780]
  simp_rw [allocEq,zeroEq]

#print axioms source_forkInit_zero32
#print axioms source_forkInit_precompile_allocation
#print axioms evaluate_forkInit_precompile_normalized
end InitECandidate.Runtime
