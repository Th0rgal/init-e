import InitECandidate.Runtime.KeyNibbleCallPreservation
import InitECandidate.Runtime.CompactNibblePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleConversion : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ (.dec _ _ _ (.seq _ (.seq body _)))))))) => body
  | _ => .skip

def compactNibbleArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.const 1],
   .op .sub [.var .local (ofString "n"),.const 1],
   .op .add [.var .local (ofString "out"),.var .local (ofString "k")]]

theorem source_compactNibble_conversion : compactNibbleConversion =
    .call (some (none,none)) (ofString "key_to_nibbles") compactNibbleArguments := by
  simp only [compactNibbleConversion,compactNibbleArguments,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual compact decoder suffix call completes the entire nibble range,
including its optional prefix, using the original modular pointer semantics. -/
theorem evaluate_compactNibble_conversion {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length out initial : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (initialLocal : state.locals.lookup (ofString "k") = some (.val (.word initial)))
    (prefixValid : TrieNibbleRange state out initial)
    (lengthBound : 2 * (length - 1).toNat + 8 < 2^64)
    (totalBound : initial.toNat + 2 * (length - 1).toNat < 2^64)
    (code : state.code = originalRuntimeCode)
    (sourceDomain : ∀ offset : Nat, offset < (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((pointer + 1) + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * (length - 1).toNat →
      state.memaddrs (panByteAlignHOL ((out + initial) + BitVec.ofNat 64 offset)))
    (ticks : (length - 1).toNat / 4 + 4 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state compactNibbleConversion
    state.clock ≤ evaluated.2.clock + ((length - 1).toNat / 4 + 4) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧
      (evaluated.1 = none → TrieNibbleRange evaluated.2 out (initial + 2 * (length - 1))) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      compactNibbleArguments = some [.val (.word (pointer + 1)),.val (.word (length - 1)),.val (.word (out + initial))] := by
    simp [compactNibbleArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal,
      outLocal,initialLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have conversion := evaluate_keyToNibbles_general_call_preserves state
    (.op .add [.var .local (ofString "p"),.const 1])
    (.op .sub [.var .local (ofString "n"),.const 1])
    (.op .add [.var .local (ofString "out"),.var .local (ofString "k")])
    (pointer + 1) (out + initial) (length - 1) out initial prefixValid lengthBound code args
    sourceDomain outputDomain ticks
  rw [source_compactNibble_conversion]
  refine ⟨conversion.1,conversion.2.1,conversion.2.2.1,?_⟩
  intro normal
  obtain ⟨suffix,prefixRange⟩ := conversion.2.2.2 normal
  apply prefixRange.concat suffix
  have doubled : (2 * (length - 1)).toNat = 2 * (length - 1).toNat := by
    rw [BitVec.toNat_mul]
    change (2 * (length - 1).toNat) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [doubled]
  exact totalBound

#print axioms evaluate_compactNibble_conversion
end InitECandidate.Runtime
