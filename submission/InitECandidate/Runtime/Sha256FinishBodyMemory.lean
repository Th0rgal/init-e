import InitECandidate.Runtime.Sha256FinishSource
import InitECandidate.Runtime.StoreBE32Memory
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.CountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaFinish_byte_separate (out index watched : BitVec 64)
    (small : index.toNat < 8) (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat) :
    ∀ offset : Nat, offset < 4 → watched ≠ panByteAlignHOL (out + index * (4#64) + BitVec.ofNat 64 offset) := by
  intro offset inside same
  have mulNatural : (index * (4#64)).toNat = index.toNat * 4 :=
    BitVec.toNat_mul_of_lt (by change index.toNat * 4 < 2 ^ 64; omega)
  have offsetNatural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have sumNatural : (index * (4#64) + BitVec.ofNat 64 offset).toNat = index.toNat * 4 + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [mulNatural,offsetNatural]; omega),mulNatural,offsetNatural]
  have cell := hashOccupancy_aligned_interval out (32#64) (index * (4#64) + BitVec.ofNat 64 offset) aligned (by change out.toNat + 32 ≤ 2 ^ 64; omega)
    (by rw [sumNatural]; change index.toNat * 4 + offset < 32; omega)
  change out.toNat ≤ _ ∧ _ < out.toNat + 32 at cell
  have natural := congrArg BitVec.toNat same
  rw [BitVec.add_assoc] at natural
  rcases outside with before | after <;> omega

theorem shaFinish_body_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer out index watched : BitVec 64)
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (small : index.toNat < 8) (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state shaFinishBody = (none,post)) :
    post.memory watched = state.memory watched ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) := by
  rw [source_shaFinish_body,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "st_be32") shaFinishArguments) with
  | mk result middle =>
    rw [called] at run
    cases result with
    | some result => cases run
    | none =>
      obtain ⟨value,memory⟩ : ∃ value : BitVec 64, state.memory (pointer + index * (8#64)) = .word value := by
        cases h : state.memory (pointer + index * (8#64)) with
        | word value => exact ⟨value,rfl⟩
      have frame : middle.memory watched = state.memory watched := by
        by_cases accessible : state.memaddrs (pointer + index * (8#64))
        · have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) shaFinishArguments =
              some [.val (.word (out + index * (4#64))),.val (.word value)] := by
            simp [shaFinishArguments,evalListHOLExact,evalHOLExact,atPointer,atOut,atIndex,wordOpHOL,wordOp,
              valueIsWord,valueWord,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,accessible,memory]
          exact storeBE32_call_normal_memory state middle _ (out + index * (4#64)) value watched args code
            (shaFinish_byte_separate out index watched small aligned fits outside) called
        · have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) shaFinishArguments = none := by
            simp [shaFinishArguments,evalListHOLExact,evalHOLExact,atPointer,atOut,atIndex,wordOpHOL,wordOp,
              valueIsWord,valueWord,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,accessible]
          rw [evaluateHOLFiniteState_call,args] at called
          cases called
      have kept := evaluate_avoidsLocal_flowing (ofString "i")
        (.call (some (none,none)) (ofString "st_be32") shaFinishArguments) rfl state
        (by rw [called]; exact Or.inl rfl)
      have metadata := evaluateHOLFiniteState_metadata state
        (.call (some (none,none)) (ofString "st_be32") shaFinishArguments)
      rw [called] at kept metadata
      have counter := (CountedBody.incr (counter := ofString "i") (step := (1 : BitVec 64))).run middle
        (metadata.1.trans code) index (kept.trans atIndex) (Nat.zero_le _)
      dsimp only at run
      rw [run] at counter
      have finalMemory := evaluate_readOnly_memory
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) rfl middle
      rw [run] at finalMemory
      exact ⟨(congrFun finalMemory watched).trans frame,(counter.2.2.2.2 rfl).1⟩

#print axioms shaFinish_byte_separate
#print axioms shaFinish_body_normal_memory
end InitECandidate.Runtime
