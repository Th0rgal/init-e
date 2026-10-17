import InitECandidate.Runtime.RlpSlicesReturnContract
import InitECandidate.Runtime.RlpSlicesAllocationUniformBound
import InitECandidate.Runtime.PanDecCallReturnedGlobalClockScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful allocation and filling retain the fixed count in the returned
slice pair, independently of the heap-global representation. -/
theorem rlpSlices_allocation_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 + 2 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesAllocation = (some (.returned value),post)) :
    ∃ array : ValueHOL 64, value = .rStruct [array,.val (.word count)] := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  have installed : state.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) (count * 16) installed
  rw [source_rlpSlices_allocation] at run
  obtain ⟨allocated,bodyPost,ready,output,bodyRun,locals,_,clock,_,_,readyCode,tail,_⟩ :=
    evaluate_decCall_returned_global_clock_scope state post (ofString "arr") (ofString "alloc") .one .one
      [argument] [.val (.word (count * 16))] (sourceFunctionBody Guest.guestFn_alloc) rlpSlicesInitialized _ value args lookup run
  have bound := evaluate_source_alloc_uniform_bounded
    (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "n",.val (.word (count * 16))))) code
    (by change 1 ≤ state.clock - 1; omega)
  rw [bodyRun] at bound
  dsimp only at bound
  have metadata := evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "n",.val (.word (count * 16)))))
    (sourceFunctionBody Guest.guestFn_alloc)
  rw [bodyRun] at metadata
  dsimp only at metadata
  let resumed := setVarHOLFinite (ofString "arr") allocated ready
  have pLocal : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "arr" ≠ ofString "p" by decide] using pointerLocal
  have cLocal : resumed.locals.lookup (ofString "count") = some (.val (.word count)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "arr" ≠ ofString "count" by decide] using countLocal
  have enough : count.toNat * 12 ≤ resumed.clock := by
    change count.toNat * 12 ≤ ready.clock
    have cost : state.clock - 1 ≤ bodyPost.clock + 1 := bound.1
    omega
  exact rlpSlices_initialized_return_contract resumed output pointer count pLocal cLocal
    (readyCode.trans (metadata.1.trans code)) enough value tail

#print axioms rlpSlices_allocation_return_contract
end InitECandidate.Runtime
