import InitECandidate.Runtime.StatelessWitnessListsBound
import InitECandidate.Runtime.SszSplitVarListFirstStage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem eval_load_mem_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) (address : BitVec 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) expression = some (.val (.word address)))
    (domain : state.memaddrs address) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one expression) = some (.val (.word (memWord state.memory address))) := by
  cases cell : state.memory address with
  | word word => simp [evalHOLExact,evaluated,isWfShapeExactHOL,memLoadHOLExact,domain,cell,memWord]

theorem source_stateless_witness_load0 : statelessAt 36 =
    .dec (ofString "w0") .one (.load .one (.var .global (ofString "ssz_offs"))) (statelessAt 37) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_load1 : statelessAt 37 =
    .dec (ofString "w1") .one (.load .one (.op .add [.var .global (ofString "ssz_offs"),.const 8])) (statelessAt 38) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_stateless_witness_load2 : statelessAt 38 =
    .dec (ofString "w2") .one (.load .one (.op .add [.var .global (ofString "ssz_offs"),.const 16])) (statelessAt 39) := by
  simp only [statelessAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual three checked witness-offset loads add no source ticks to
the input-length bound for all subsequent witness-list decoding. -/
theorem evaluate_stateless_witness_loads_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets first middle last heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (domain0 : state.memaddrs offsets) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16))
    (read0 : memWord state.memory offsets = first)
    (read8 : memWord state.memory (offsets + 8) = middle)
    (read16 : memWord state.memory (offsets + 16) = last)
    (ordered0 : first.toNat ≤ middle.toNat) (ordered1 : middle.toNat ≤ last.toNat)
    (ordered2 : last.toNat ≤ length.toNat) (budget : length.toNat + 12 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 36)
    state.clock ≤ evaluated.2.clock + (length.toNat + 12) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let one := setVarHOLFinite (ofString "w0") (.val (.word first)) state
  let two := setVarHOLFinite (ofString "w1") (.val (.word middle)) one
  let ready := setVarHOLFinite (ofString "w2") (.val (.word last)) two
  have load0 := eval_load_mem_word state (.var .global (ofString "ssz_offs")) offsets
    (by simp [evalHOLExact,atOffsets]) domain0
  rw [read0] at load0
  have load1 := eval_load_mem_word one (.op .add [.var .global (ofString "ssz_offs"),.const 8]) (offsets + 8)
    (by simp [one,setVarHOLFinite,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord]) domain8
  change @evalHOLExact 64 F _ one.toExact (fun a => Classical.propDecidable (one.memaddrs a)) _ =
    some (.val (.word (memWord state.memory (offsets + 8)))) at load1
  rw [read8] at load1
  have load2 := eval_load_mem_word two (.op .add [.var .global (ofString "ssz_offs"),.const 16]) (offsets + 16)
    (by simp [two,one,setVarHOLFinite,evalHOLExact,evalListHOLExact,atOffsets,wordOpHOL,wordOp,valueIsWord,valueWord]) domain16
  change @evalHOLExact 64 F _ two.toExact (fun a => Classical.propDecidable (two.memaddrs a)) _ =
    some (.val (.word (memWord state.memory (offsets + 16)))) at load2
  rw [read16] at load2
  rw [source_stateless_witness_load0]
  apply evaluate_dec_word_post state (ofString "w0") _ _ first _ (fun r _ => r ≠ some .timeOut)
    (fun _ _ _ h => h) load0
  rw [source_stateless_witness_load1]
  apply evaluate_dec_word_post one (ofString "w1") _ _ middle _ (fun r _ => r ≠ some .timeOut)
    (fun _ _ _ h => h) load1
  rw [source_stateless_witness_load2]
  apply evaluate_dec_word_post two (ofString "w2") _ _ last _ (fun r _ => r ≠ some .timeOut)
    (fun _ _ _ h => h) load2
  have kept : ∀ key, key ≠ ofString "w0" → key ≠ ofString "w1" → key ≠ ofString "w2" →
      ready.locals.lookup key = state.locals.lookup key := by
    intro key n0 n1 n2
    simp [ready,two,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n0,Ne.symm n1,Ne.symm n2]
  apply evaluate_stateless_witness_lists_input_bounded ready pointer first middle last length heapPointer
    ((kept _ (by decide) (by decide) (by decide)).trans atPointer) ?_ ?_ ?_
    ((kept _ (by decide) (by decide) (by decide)).trans atLength) heap heapBound code ordered0 ordered1 ordered2 budget
  all_goals simp [ready,two,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "w1" ≠ ofString "w0" by decide,show ofString "w2" ≠ ofString "w0" by decide,
    show ofString "w2" ≠ ofString "w1" by decide]

#print axioms eval_load_mem_word
#print axioms evaluate_stateless_witness_loads_bounded
end InitECandidate.Runtime
