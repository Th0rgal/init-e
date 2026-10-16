import InitECandidate.Runtime.MemzeroCoverage
import InitECandidate.Runtime.MemzeroWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real eight-byte body extends the byte invariant and advances the
counter while preserving the clock and all non-memory runtime fields. -/
theorem evaluate_memzero_word8_coverage {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : state.memaddrs (destination + index))
    (zero : ZeroBytePrefix state destination index.toNat)
    (aligned : (destination.toNat + index.toNat) % 8 = 0)
    (bounded : destination.toNat + index.toNat + 8 ≤ 2 ^ 64) :
    ∃ post, evaluateHOLFiniteState state memzeroWord8Body = (none,post) ∧
      ZeroBytePrefix post destination (index.toNat + 8) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 8))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.be = state.be ∧ ∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name := by
  let post := setVarHOLFinite (ofString "i") (.val (.word (index + 8))) (sourceWriteWord state (destination + index) 0)
  have covered := ZeroBytePrefix.extend_word state destination index.toNat zero aligned bounded
    (by simpa using domain)
  refine ⟨post,evaluate_memzero_word8_body state destination index dstLocal indexLocal domain,?_,rfl,?_,rfl,rfl,rfl,rfl,?_⟩
  · change ZeroBytePrefix (sourceWriteWord state (destination + index) 0) destination (index.toNat + 8)
    simpa using covered
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    have backwards := Ne.symm different
    simp [post,setVarHOLFinite,sourceWriteWord,HolFiniteMapExact.lookup_update,FUPDATE,backwards]

/-- Evaluate the actual block guard without expanding word comparison into
large arithmetic expressions inside a later whole-loop kernel proof. -/
theorem eval_memzero_block_condition {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size stride : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memzeroBlockCondition stride) =
        some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .notLower size (index + stride) then 1 else 0))) := by
  have added : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .add [.var .local (ofString "i"),.const stride]) = some (.val (.word (index + stride))) := by
    simp [evalHOLExact,evalListHOLExact,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  unfold memzeroBlockCondition
  rw [evalHOLExact]
  rw [added]
  simp only [evalHOLExact]
  rw [sizeLocal]

#print axioms evaluate_memzero_word8_coverage
#print axioms eval_memzero_block_condition
end InitECandidate.Runtime
