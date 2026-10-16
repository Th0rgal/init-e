import InitECandidate.Runtime.HashInsertCountTail
import InitECandidate.Runtime.AllocationRound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def htabNewDecodedBody : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_htab_new with | .function fn => fn.body | _ => .skip

def htabNewAfterHeader : ProgHOL 64 :=
  match htabNewDecodedBody with
  | .decCall _ _ _ _ (.dec _ _ _ (.seq _ (.seq _ (.seq _ (.seq _ rest))))) => rest
  | _ => .skip

def htabNewStrideExpression : ExpHOL 64 :=
  .op .and [.op .add [.var .local (ofString "key_len"),.const 7],.op .sub [.const 0,.const 8]]

def htabNewHeader (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (hashLocalAddress (ofString "t") 0) (.var .local (ofString "key_len")))
    (.seq (.store (hashLocalAddress (ofString "t") 8) (.var .local (ofString "stride")))
      (.seq (.store (hashLocalAddress (ofString "t") 16) (.var .local (ofString "cap")))
        (.seq (.store (hashLocalAddress (ofString "t") 24) (.const 0)) continuation)))

/-- The actual constructor first allocates its header, computes stride and
writes the four scalar fields before allocating its arrays. -/
theorem source_htabNew_header : sourceFunctionBody Guest.guestFn_htab_new =
    .decCall (ofString "t") .one (ofString "alloc") [.const 72]
      (.dec (ofString "stride") .one htabNewStrideExpression (htabNewHeader htabNewAfterHeader)) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_htab_new,declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,
    expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,
    htabNewAfterHeader,htabNewDecodedBody,htabNewStrideExpression,htabNewHeader,hashLocalAddress]
  rfl

noncomputable def htabNewHeaderPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength stride capacity : BitVec 64) :=
  sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord state
    (table + 0) keyLength) (table + 8) stride) (table + 16) capacity) (table + 24) 0

/-- The complete literal header-writing prefix enters its continuation with
zero item count and the requested key length, stride and capacity. -/
theorem evaluate_htabNew_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength stride capacity : BitVec 64) (continuation : ProgHOL 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain0 : state.memaddrs (table + 0)) (domain8 : state.memaddrs (table + 8))
    (domain16 : state.memaddrs (table + 16)) (domain24 : state.memaddrs (table + 24)) :
    evaluateHOLFiniteState state (htabNewHeader continuation) =
      evaluateHOLFiniteState (htabNewHeaderPost state table keyLength stride capacity) continuation := by
  let one := sourceWriteWord state (table + 0) keyLength
  let two := sourceWriteWord one (table + 8) stride
  let three := sourceWriteWord two (table + 16) capacity
  have store0 := evaluate_store_word state (table + 0) keyLength _ (.var .local (ofString "key_len"))
    (eval_hashLocalAddress state (ofString "t") table 0 tableLocal) keyLocal domain0
  have store8 := evaluate_store_word one (table + 8) stride _ (.var .local (ofString "stride"))
    (eval_hashLocalAddress one (ofString "t") table 8 tableLocal) strideLocal domain8
  have store16 := evaluate_store_word two (table + 16) capacity _ (.var .local (ofString "cap"))
    (eval_hashLocalAddress two (ofString "t") table 16 tableLocal) capLocal domain16
  have store24 := evaluate_store_word three (table + 24) 0 _ (.const 0)
    (eval_hashLocalAddress three (ofString "t") table 24 tableLocal) (by rfl) domain24
  unfold htabNewHeader
  rw [evaluateHOLFiniteState_seq_line780,store0]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,store8]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,store16]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,store24]
  rfl

theorem htabNewHeaderPost_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength stride capacity : BitVec 64) :
    (htabNewHeaderPost state table keyLength stride capacity).memory (table + 0) = .word keyLength ∧
    (htabNewHeaderPost state table keyLength stride capacity).memory (table + 8) = .word stride ∧
    (htabNewHeaderPost state table keyLength stride capacity).memory (table + 16) = .word capacity ∧
    (htabNewHeaderPost state table keyLength stride capacity).memory (table + 24) = .word 0 ∧
    (htabNewHeaderPost state table keyLength stride capacity).clock = state.clock ∧
    (htabNewHeaderPost state table keyLength stride capacity).locals = state.locals := by
  simp [htabNewHeaderPost,sourceWriteWord]

/-- Exact constructor stride computation, using the allocator's already
verified rounding expression with a zero base pointer. -/
theorem eval_htabNew_stride {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) htabNewStrideExpression =
        some (.val (.word (allocationEnd 0 keyLength))) := by
  simp [htabNewStrideExpression,evalHOLExact,evalListHOLExact,keyLocal,wordOpHOL,wordOp,
    valueIsWord,valueWord,allocationEnd]
  change (keyLength + 7) &&& ((0 - 8) &&& BitVec.allOnes 64) = _
  rw [BitVec.and_allOnes]
  rfl

/-- The challenge's key widths fit in at most56 aligned bytes per table slot. -/
theorem htabNew_stride_bound (keyLength : BitVec 64) (small : keyLength.toNat ≤ 52) :
    keyLength.toNat ≤ (allocationEnd 0 keyLength).toNat ∧
      (allocationEnd 0 keyLength).toNat ≤ 56 ∧ (allocationEnd 0 keyLength).toNat % 8 = 0 := by
  have rounded := allocationEnd_covers 0 keyLength (by change 0 + keyLength.toNat ≤ 33806089496; omega)
  change keyLength.toNat ≤ _ ∧ _ ≤ 56 ∧ _ % 8 = 0
  change 0 + keyLength.toNat ≤ _ ∧ _ < 0 + keyLength.toNat + 8 ∧ _ % 8 = 0 at rounded
  omega

#print axioms htabNewHeaderPost_fields
#print axioms eval_htabNew_stride
#print axioms htabNew_stride_bound
#print axioms source_htabNew_header
#print axioms evaluate_htabNew_header
end InitECandidate.Runtime
