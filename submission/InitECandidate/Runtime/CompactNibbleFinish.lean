import InitECandidate.Runtime.CompactNibbleConversion
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleFinish : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ (.dec _ _ _ (.seq _ body))))))) => body
  | _ => .skip

def compactNibbleReturnValue (out initial length leaf : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word out),.val (.word (initial + 2 * (length - 1))),.val (.word leaf)]

theorem source_compactNibble_finish : compactNibbleFinish = .seq compactNibbleConversion
    (.return (.rstruct [.var .local (ofString "out"),
      .op .add [.var .local (ofString "k"),.panop .mul [.const 2,
        .op .sub [.var .local (ofString "n"),.const 1]]],
      .var .local (ofString "is_leaf")])) := by
  simp only [compactNibbleFinish,compactNibbleConversion,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual final conversion and structured return expose the valid path
at precisely the pointer and length returned to the trie parser. -/
theorem evaluate_compactNibble_finish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial leaf : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (initialLocal : state.locals.lookup (ofString "k") = some (.val (.word initial)))
    (leafLocal : state.locals.lookup (ofString "is_leaf") = some (.val (.word leaf)))
    (prefixValid : TrieNibbleRange state out initial)
    (lengthBound : 2 * (length - 1).toNat + 8 < 2^64)
    (totalBound : initial.toNat + 2 * (length - 1).toNat < 2^64)
    (code : state.code = originalRuntimeCode)
    (sourceDomain : ∀ offset : Nat, offset < (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((pointer + 1) + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((out + initial) + BitVec.ofNat 64 offset)))
    (ticks : (length - 1).toNat / 4 + 4 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state compactNibbleFinish = (result,post) ∧
      state.clock ≤ post.clock + ((length - 1).toNat / 4 + 4) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        value = compactNibbleReturnValue out initial length leaf ∧
        TrieNibbleRange post out (initial + 2 * (length - 1))) := by
  have bound := evaluate_compactNibble_conversion state pointer length out initial
    pointerLocal lengthLocal outLocal initialLocal prefixValid lengthBound totalBound code sourceDomain outputDomain ticks
  generalize run : evaluateHOLFiniteState state compactNibbleConversion = evaluated at bound
  obtain ⟨result,middle⟩ := evaluated
  obtain ⟨cost,remaining,noTimeout,valid⟩ := bound
  rw [source_compactNibble_finish,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | some stopped =>
    refine ⟨_,_,rfl,cost,remaining,noTimeout,?_⟩
    intro value returned
    have noReturn : ∀ v, (evaluateHOLFiniteState state compactNibbleConversion).1 ≠ some (.returned v) := by
      rw [source_compactNibble_conversion]
      intro v
      exact evaluate_discard_call_no_return state (ofString "key_to_nibbles") compactNibbleArguments v
    exact False.elim (noReturn value (by rw [run]; exact returned))
  | none =>
    have locals : middle.locals = state.locals := by
      have success : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "key_to_nibbles") compactNibbleArguments)).1 = none := by
        rw [← source_compactNibble_conversion,run]
      have frame := evaluate_discard_call_success_locals state (ofString "key_to_nibbles") compactNibbleArguments success
      rw [← source_compactNibble_conversion,run] at frame
      exact frame
    have returned : @evalHOLExact 64 F _ middle.toExact
        (fun address => Classical.propDecidable (middle.memaddrs address))
        (.rstruct [.var .local (ofString "out"),
          .op .add [.var .local (ofString "k"),.panop .mul [.const 2,
            .op .sub [.var .local (ofString "n"),.const 1]]],
          .var .local (ofString "is_leaf")]) = some (compactNibbleReturnValue out initial length leaf) := by
      simp [evalHOLExact,evalListHOLExact,locals,outLocal,initialLocal,lengthLocal,leafLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL,compactNibbleReturnValue]
    dsimp only
    rw [evaluateHOLFiniteState_return,returned]
    simp only [compactNibbleReturnValue,shapeOfHOLExact,sizeOfShapeWithContextHOL,List.map]
    refine ⟨_,_,rfl,cost,remaining,by simp,?_⟩
    intro value equal
    have valueEq : value = compactNibbleReturnValue out initial length leaf := by simpa [compactNibbleReturnValue] using equal.symm
    exact ⟨valueEq,(valid rfl).after_frame rfl rfl rfl⟩

#print axioms evaluate_compactNibble_finish
end InitECandidate.Runtime
