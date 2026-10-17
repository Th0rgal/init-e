import InitECandidate.Runtime.RlpFailCallBound
import InitECandidate.Runtime.DiscardCallNoReturn
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemAfterByte : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_item with
  | .seq _ (.dec _ _ _ body) => body
  | _ => .skip

def rlpItemAfterSingleByte : ProgHOL 64 :=
  match rlpItemAfterByte with
  | .seq _ body => body
  | _ => .skip

theorem source_rlpItem_body : sourceFunctionBody Guest.guestFn_rlp_item =
    .seq (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip)
      (.dec (ofString "b") .one (.loadByte (.var .local (ofString "p"))) rlpItemAfterByte) := by
  simp only [rlpItemAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpItem_single_byte : rlpItemAfterByte =
    .seq (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
      (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) rlpItemAfterSingleByte := by
  simp only [rlpItemAfterByte,rlpItemAfterSingleByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original one-byte RLP case returns immediately without any nested
call or source-clock debit; later string/list branches are unreachable. -/
theorem evaluate_rlpItem_single_byte_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (small : header.toNat < 128) :
    evaluateHOLFiniteState state rlpItemAfterByte =
      (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),.val (.word pointer),.val (.word 1),.val (.word 1)])),
        emptyLocalsHOLFinite state) := by
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "b")) (.const 128)) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,small]
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
  simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,pointerLocal,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- The full original single-byte path includes the nonempty check, actual
header read and scoped byte binding, and preserves memory and globals. -/
theorem evaluate_rlpItem_single_byte_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (small : byte.toNat < 128)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) =
      (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),.val (.word pointer),.val (.word 1),.val (.word 1)])),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals := by
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b" ≠ ofString "p" by decide] using pointerLocal
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have run := evaluate_rlpItem_single_byte_after_load entered pointer (BitVec.ofNat 64 byte.toNat) atPointer atByte
    (by change byte.toNat % 2^64 < 128; omega)
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  refine ⟨{emptyLocalsHOLFinite entered with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite entered).locals (ofString "b",state.locals.lookup (ofString "b"))},?_,rfl,rfl,rfl⟩
  rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check]
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,pointerLocal,loaded,Option.map_some,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpItemAfterByte; _) = _
  rw [run]

/-- Empty RLP input takes the original rlp_fail(1) call before any header
load, spending one tick and never returning an item. -/
theorem evaluate_rlpItem_empty_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word (0 : BitVec 64))))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item)
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none ∧
      (∀ value, evaluated.1 ≠ some (.returned value)) := by
  have bound := evaluate_rlpFail_call_bounded state (.const 1) 1 code (by omega) (by rfl)
  have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 1]
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) with
  | mk result post =>
    rw [run] at bound noReturn
    dsimp only at bound noReturn
    cases result with
    | none => exact False.elim (bound.2.2 rfl)
    | some stopped => exact ⟨bound.1,bound.2.1,bound.2.2,noReturn⟩

/-- An unreadable initial byte stops the original item parser immediately,
without entering later cases or spending any source clock. -/
theorem evaluate_rlpItem_unreadable_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = none) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some .error,state) := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check]
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  simp [evalHOLExact,pointerLocal,loaded]

#print axioms evaluate_rlpItem_empty_body
#print axioms evaluate_rlpItem_unreadable_header
#print axioms evaluate_rlpItem_single_byte_after_load
#print axioms evaluate_rlpItem_single_byte_body
end InitECandidate.Runtime
