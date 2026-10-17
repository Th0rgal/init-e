import InitECandidate.Runtime.KeyToNibblesGeneralTailRange
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibblePrefix : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_compact_to_nibbles with
  | .seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ (.dec _ _ _ (.seq body _))))))) => body
  | _ => .skip

theorem source_compactNibble_prefix : compactNibblePrefix =
    .ite (.cmp .notEqual (.var .local (ofString "odd")) (.const 0))
      (.seq (.storeByte (.var .local (ofString "out"))
        (.op .and [.var .local (ofString "c0"),.const 15]))
        (.assign .local (ofString "k") (.const 1))) .skip := by
  simp only [compactNibblePrefix,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual optional first-nibble write establishes its output prefix and
sets the exact length used by the following conversion call. -/
theorem evaluate_compactNibble_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (out c0 odd : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (byteLocal : state.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (oddLocal : state.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (kLocal : state.locals.lookup (ofString "k") = some (.val (.word (0 : BitVec 64))))
    (domain : state.memaddrs (panByteAlignHOL out)) :
    ∃ post, evaluateHOLFiniteState state compactNibblePrefix = (none,post) ∧
      post.clock = state.clock ∧
      post.locals.lookup (ofString "k") = some (.val (.word (if odd = 0 then 0 else 1))) ∧
      TrieNibbleRange post out (if odd = 0 then 0 else 1) ∧
      post.memaddrs = state.memaddrs ∧ post.code = state.code ∧
      (∀ name, name ≠ ofString "k" → post.locals.lookup name = state.locals.lookup name) := by
  rw [source_compactNibble_prefix,evaluateHOLFiniteState_ite]
  by_cases zero : odd = 0
  · simp [evalHOLExact,oddLocal,Compiler.Encoders.Asm.wordCmpHOL,zero,evaluateHOLFiniteState_skip]
    refine ⟨by simpa using kLocal,?_⟩
    intro offset inside
    simp at inside
  · have zeroNat : odd ≠ BitVec.ofNat 64 0 := by exact zero
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.var .local (ofString "odd")) (.const 0)) = some (.val (.word 1)) := by
      simp [evalHOLExact,oddLocal,Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    rw [guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,reduceIte]
    obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64, state.memory (panByteAlignHOL out) = .word cell := by
      cases state.memory (panByteAlignHOL out) with
      | word cell => exact ⟨cell,rfl⟩
    have address : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.var .local (ofString "out")) = some (.val (.word (out + 0))) := by simpa [evalHOLExact] using outLocal
    have value : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .and [.var .local (ofString "c0"),.const 15]) = some (.val (.word (c0 &&& 15))) := by
      simp [evalHOLExact,evalListHOLExact,byteLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
      change c0 &&& ((15 : BitVec 64) &&& 18446744073709551615) = _
      bv_decide
    obtain ⟨middle,store,range,clock⟩ := evaluate_nibble_append_no_wrap state
      (.var .local (ofString "out")) (.op .and [.var .local (ofString "c0"),.const 15])
      out 0 (c0 &&& 15) cell (by intro offset inside; simp at inside) (by decide)
      (keyNibble_low_small c0) address value (by simpa using domain) (by simpa using cellRead)
    have locals : middle.locals = state.locals := by
      have exactStore := evaluate_source_storeByte state (.var .local (ofString "out"))
        (.op .and [.var .local (ofString "c0"),.const 15]) out (c0 &&& 15) cell
        (by simpa using address) value domain cellRead
      have same := Prod.mk.inj (store.symm.trans exactStore)
      simpa only [sourceWriteByte] using congrArg (fun s : PanSemStateFiniteExact 64 F => s.locals) same.2
    have metadata := evaluateHOLFiniteState_metadata state
      (.storeByte (.var .local (ofString "out")) (.op .and [.var .local (ofString "c0"),.const 15]))
    rw [store] at metadata
    dsimp only at metadata
    have assignment := evaluate_local_word_assignment middle (ofString "k") (.const 1) 0 1
      (by rw [locals]; exact kLocal) (by rfl)
    rw [evaluateHOLFiniteState_seq_line780,store]
    dsimp only
    rw [assignment]
    refine ⟨_,rfl,clock,?_,?_,metadata.2.1,metadata.1,?_⟩
    · simp [zeroNat,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simpa [zeroNat] using range.after_frame (show (setVarHOLFinite (ofString "k") (.val (.word (1 : BitVec 64))) middle).memory = middle.memory from rfl) rfl rfl

    · intro name different
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different] using congrArg (fun ls => ls.lookup name) locals

#print axioms evaluate_compactNibble_prefix
end InitECandidate.Runtime
