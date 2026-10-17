import InitECandidate.Runtime.DecodeStepExtensionStores
import InitECandidate.Runtime.ScratchAllocationCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_decodeStep_extension_record : decodeStepExtensionRecord =
    .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88] decodeStepExtensionStores := by
  simp only [decodeStepExtensionRecord,decodeStepExtensionStores,decodeStepExtensionSuffix,
    decodeStepCompactContinuation,decodeStepCompactCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The real parser allocates and fills its extension continuation record in
one source tick, retaining the decoded path under the stated scratch separation. -/
theorem evaluate_decodeStep_extension_record {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch frame arr pointer length nibs count leaf : BitVec 64)
    (arrLocal : state.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (pathLocal : state.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (valid : TrieNibbleRange state nibs count)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (request : (88 : BitVec 64) ≤ scratch - frame)
    (within : frame ≤ scratchAllocationEnd scratch 88)
    (domain : ∀ offset ∈ ([8,24,48,56,64,72] : List Nat),
      state.memaddrs (scratchAllocationEnd scratch 88 + BitVec.ofNat 64 offset))
    (outside : ∀ offset : Nat, offset < count.toNat → ∀ field ∈ ([8,24,48,56,64,72] : List Nat),
      panByteAlignHOL (nibs + BitVec.ofNat 64 offset) ≠ scratchAllocationEnd scratch 88 + BitVec.ofNat 64 field) :
    ∃ post, evaluateHOLFiniteState state decodeStepExtensionRecord =
        (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word (scratchAllocationEnd scratch 88))])),post) ∧
      post.clock = state.clock - 1 ∧ TrieNibbleRange post nibs count ∧
      post.memory (scratchAllocationEnd scratch 88 + 64) = .word nibs ∧
      post.memory (scratchAllocationEnd scratch 88 + 72) = .word count := by
  let record := scratchAllocationEnd scratch 88
  obtain ⟨ready,_,clock,memory,locals,_,addresses,_,endian,_,declaration⟩ :=
    evaluate_scratch_alloc_call_and_declaration state (.const 88) scratch 88 frame (by rfl) code
      (by omega) scratchGlobal frameGlobal request within
  let entered := setVarHOLFinite (ofString "rec") (.val (.word record)) ready
  have localFrame : ∀ name, name ≠ ofString "rec" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atRecord : entered.locals.lookup (ofString "rec") = some (.val (.word record)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredValid : TrieNibbleRange entered nibs count := valid.after_frame memory addresses endian
  have run := evaluate_decodeStep_extension_stores entered record arr pointer length nibs count leaf atRecord
    ((localFrame _ (by decide)).trans arrLocal) ((localFrame _ (by decide)).trans pointerLocal)
    ((localFrame _ (by decide)).trans lengthLocal) ((localFrame _ (by decide)).trans pathLocal)
    (by simpa only [entered,setVarHOLFinite,addresses,record] using domain)
  have preserved := decodeStepExtensionStoresPost_path entered record arr pointer length nibs count enteredValid outside
  let output := decodeStepExtensionStoresPost entered record arr pointer length nibs count
  let final := {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "rec",state.locals.lookup (ofString "rec"))}
  refine ⟨final,?_,preserved.2.2.2.trans clock,preserved.1.after_frame rfl rfl rfl,preserved.2.1,preserved.2.2.1⟩
  rw [source_decodeStep_extension_record,declaration]
  change (let result := evaluateHOLFiniteState entered decodeStepExtensionStores; _) = _
  rw [run]

#print axioms evaluate_decodeStep_extension_record
end InitECandidate.Runtime
