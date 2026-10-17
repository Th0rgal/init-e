import InitECandidate.Runtime.KeyToNibblesOffsetPair
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute a real source load and its two stores before the continuation.
The load observes the current memory, allowing earlier writes to overlap it. -/
theorem evaluate_keyNibble_byte_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (continuation : ProgHOL 64) (key out index : BitVec 64)
    (notOut : name ≠ ofString "out") (notIndex : name ≠ ofString "i")
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (bounded : (2 * index + BitVec.ofNat 64 (2 * offset)).toNat < 63)
    (valid : TrieNibbleRange state out (2 * index + BitVec.ofNat 64 (2 * offset)))
    (sourceDomain : state.memaddrs (panByteAlignHOL (key + (index + BitVec.ofNat 64 offset))))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 (2 * offset)))))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 (2 * offset)) + 1)))) :
    ∃ (byte : UInt8) (middle : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState state (keyNibbleByteThen name offset continuation) =
        (let result := evaluateHOLFiniteState middle continuation
         (result.1,{result.2 with locals := HolFiniteMapExact.resVarEq result.2.locals (name,state.locals.lookup name)})) ∧
      TrieNibbleRange middle out (2 * index + BitVec.ofNat 64 (2 * offset) + 1 + 1) ∧
      middle.locals = (setVarHOLFinite name (.val (.word (BitVec.ofNat 64 byte.toNat))) state).locals ∧
      middle.clock = state.clock ∧ middle.memaddrs = state.memaddrs ∧ middle.be = state.be := by
  obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64,
      state.memory (panByteAlignHOL (key + (index + BitVec.ofNat 64 offset))) = .word cell := by
    cases state.memory (panByteAlignHOL (key + (index + BitVec.ofNat 64 offset))) with
    | word cell => exact ⟨cell,rfl⟩
  let byte := panGetByteHOL (key + (index + BitVec.ofNat 64 offset)) cell state.be
  have loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (key + (index + BitVec.ofNat 64 offset)) = some byte := by
    simp [panMemLoadByteHOL,sourceDomain,cellRead,byte]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.op .add ([.var .local (ofString "key"),.var .local (ofString "i")] ++
        if offset = 0 then [] else [.const (BitVec.ofNat 64 offset)]))) =
      some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    by_cases zero : offset = 0
    · subst offset
      have loadedZero : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
          (fun address => Classical.propDecidable (state.memaddrs address)) state.be (key + index) = some byte := by simpa using loaded
      simp [evalHOLExact,evalListHOLExact,keyLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,loadedZero]
    · simp [evalHOLExact,evalListHOLExact,keyLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,zero,loaded]
  let entered := setVarHOLFinite name (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have outEntered : entered.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notOut] using outLocal
  have indexEntered : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notIndex] using indexLocal
  have byteEntered : entered.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨middle,bodyRun,range,locals,clock,domain,endian⟩ :=
    evaluate_keyNibble_prefix_then entered name (2 * offset) byte continuation out index
      outEntered indexEntered byteEntered bounded (valid.after_frame rfl rfl rfl) firstDomain secondDomain
  refine ⟨byte,middle,?_,range,locals,clock,domain,endian⟩
  rw [keyNibbleByteThen,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered (keyNibbleStoresThen name (2 * offset) continuation); _) = _
  rw [bodyRun]

#print axioms evaluate_keyNibble_byte_scope
end InitECandidate.Runtime
