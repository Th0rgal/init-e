import InitECandidate.Runtime.RlpHeaderShortListFullContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpHeaderSingleValue : ValueHOL 64 :=
  .rStruct [.val (.word 0),.val (.word 1),.val (.word 0)]

theorem source_rlpHeader_single_branch : rlpHeaderSingleBranch =
    .return (.rstruct [.const 0,.const 1,.const 0]) := by
  simp only [rlpHeaderSingleBranch,rlpHeaderAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The single-byte header returns its exact fields without spending source ticks. -/
theorem evaluate_rlpHeader_single_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (small : header.toNat < 128) :
    evaluateHOLFiniteState state rlpHeaderAfterByte =
      (some (.returned rlpHeaderSingleValue),emptyLocalsHOLFinite state) := by
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,small]
  rw [source_rlpHeaderSingle_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  rw [source_rlpHeader_single_branch]
  simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,rlpHeaderSingleValue,
    shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- Full single-byte header parsing needs no clock premise and consumes one
input byte; the byte scope preserves memory, globals and source clock. -/
theorem evaluate_rlpHeader_single_full {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (small : byte.toNat < 128)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) =
        (some (.returned rlpHeaderSingleValue),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      1 ≤ length.toNat := by
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have run := evaluate_rlpHeader_single_after_load entered (BitVec.ofNat 64 byte.toNat) atByte
    (by change byte.toNat % 2^64 < 128; omega)
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  let final := {emptyLocalsHOLFinite entered with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite entered).locals (ofString "b",state.locals.lookup (ofString "b"))}
  refine ⟨final,?_,rfl,rfl,rfl,?_⟩
  · rw [source_rlpHeader_body,evaluateHOLFiniteState_seq_line780,check]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,pointerLocal,loaded,Option.map_some,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered rlpHeaderAfterByte; _) = _
    rw [run]
  · by_contra bad
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show length.toNat = 0 by omega)

#print axioms evaluate_rlpHeader_single_after_load
#print axioms evaluate_rlpHeader_single_full
end InitECandidate.Runtime
