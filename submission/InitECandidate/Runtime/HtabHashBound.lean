import InitECandidate.Runtime.HashBody32
import InitECandidate.Runtime.LocalBoundLoop
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.PanDecCallReadFrame
import InitECandidate.Runtime.OriginalHashCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htabHashWordLoop : ProgHOL 64 :=
  match hashAfterAlignment with | .dec _ _ _ (.seq (.while _ body) _) => body | _ => .skip
def htabHashByteLoop : ProgHOL 64 :=
  match hashAfterAlignment with | .dec _ _ _ (.seq _ (.seq (.while _ body) _)) => body | _ => .skip
def htabHashMix : ProgHOL 64 :=
  match hashAfterAlignment with | .dec _ _ _ (.seq _ (.seq _ rest)) => rest | _ => .skip

theorem source_htabHash_after : hashAfterAlignment =
    .dec (ofString "i") .one (.const 0)
      (.seq (.while (.cmp .notLower (.var .local (ofString "key_len")) (.op .add [.var .local (ofString "i"),.const 8]))
          htabHashWordLoop)
        (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "key_len"))) htabHashByteLoop)
          htabHashMix)) := by rfl

theorem htabHash_prefix_straight :
    extStraightLine (.ite hashAlignmentCondition hashAlignedBody hashUnalignedBody) = true := by decide
theorem htabHash_prefix_keeps :
    avoidsLocal (ofString "key_len") (.ite hashAlignmentCondition hashAlignedBody hashUnalignedBody) = true := by decide
theorem htabHash_mix_straight : extStraightLine htabHashMix = true := by decide
theorem htabHash_wordLoop_counted : CountedBody (ofString "i") 8 htabHashWordLoop (0 + (0 + 0)) :=
  CountedBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide)
    (CountedBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide) CountedBody.incr)
theorem htabHash_byteLoop_counted : CountedBody (ofString "i") 1 htabHashByteLoop (0 + 0) :=
  CountedBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide) CountedBody.incr
theorem htabHash_wordLoop_keeps : avoidsLocal (ofString "key_len") htabHashWordLoop = true := by decide
theorem htabHash_byteLoop_keeps : avoidsLocal (ofString "key_len") htabHashByteLoop = true := by decide
theorem htabHash_wordLoop_noBreak : noTopBreak htabHashWordLoop = true := by decide
theorem htabHash_byteLoop_noBreak : noTopBreak htabHashByteLoop = true := by decide

/-- `htab_hash` from any state whose `key_len` local is a word below 2^62 spends
at most key_len / 8 + 8 ticks in every outcome (any pointer, alignment or
readability; unreadable key bytes end the run with an error). -/
theorem evaluate_htabHash_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (keyLength : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (small : keyLength.toNat < 2 ^ 62) (budget : keyLength.toNat / 8 + 8 ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_hash) (keyLength.toNat / 8 + 8) := by
  rw [source_hash_scoped_body]
  apply RunBounded.decConst
  apply RunBounded.decConst
  generalize hseed : setVarHOLFinite (ofString "w") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "h") (.val (.word (14695981039346656037 : BitVec 64))) state) = seeded
  have seededCode : seeded.code = originalRuntimeCode := by rw [← hseed]; exact code
  have seededClock : seeded.clock = state.clock := by rw [← hseed]; rfl
  have seededLength : seeded.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    rw [← hseed]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "w" ≠ ofString "key_len" by decide,show ofString "h" ≠ ofString "key_len" by decide,lengthLocal]
  rw [show keyLength.toNat / 8 + 8 = 0 + (keyLength.toNat / 8 + 8) by omega]
  refine RunBounded.seq (RunBounded.ofProg (ProgBounded.straight _ htabHash_prefix_straight) seededCode (Nat.zero_le _))
    (by omega) ?_
  intro next run nextCode nextBudget
  have nextLength : next.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    have kept := evaluate_avoidsLocal_flowing (ofString "key_len") _ htabHash_prefix_keeps seeded (by rw [run]; exact Or.inl rfl)
    rw [run] at kept
    rw [kept]; exact seededLength
  rw [source_htabHash_after]
  apply RunBounded.decConst
  generalize hentry : setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) next = entry
  have entryCode : entry.code = originalRuntimeCode := by rw [← hentry]; exact nextCode.trans seededCode
  have entryClock : entry.clock = next.clock := by rw [← hentry]; rfl
  have entryCounter : entry.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    rw [← hentry]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryLength : entry.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    rw [← hentry]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "key_len" by decide,nextLength]
  have words := localBoundWhile_run (ofString "i") (ofString "key_len") 8 keyLength LocalBoundTest.fits
    (by simp; omega) (by decide) htabHash_wordLoop_counted htabHash_wordLoop_keeps htabHash_wordLoop_noBreak
    entry entryCode 0 entryCounter entryLength (by decide) (by simp; omega)
  apply RunBounded.weaken (cost := (keyLength.toNat - (0 : BitVec 64).toNat + (8 : BitVec 64).toNat - 1) / (8 : BitVec 64).toNat * (0 + (0 + 0) + 1) + (7 + 0))
  · refine RunBounded.seq ⟨words.1,words.2.1,words.2.2.1⟩ (by simp; omega) ?_
    intro after loopRun afterCode afterBudget
    have exited := words.2.2.2
    rw [loopRun] at exited
    obtain ⟨_,w',atCounter,atLength,beyond,below⟩ := exited rfl
    have bytes := localBoundWhile_run (ofString "i") (ofString "key_len") 1 keyLength
      (LocalBoundTest.below .lower (Or.inr rfl)) (by simp; omega) (by decide) htabHash_byteLoop_counted
      htabHash_byteLoop_keeps htabHash_byteLoop_noBreak after (afterCode.trans entryCode) w' atCounter atLength below
      (by simp at beyond ⊢; omega)
    refine RunBounded.seq (RunBounded.weaken ⟨bytes.1,bytes.2.1,bytes.2.2.1⟩ (by simp at beyond ⊢; omega)) (by omega) ?_
    intro final _ finalCode _
    exact RunBounded.ofProg (ProgBounded.straight _ htabHash_mix_straight)
      (finalCode.trans (afterCode.trans entryCode)) (Nat.zero_le _)
  · simp; omega

#print axioms evaluate_htabHash_body_bounded

theorem htabHash_readOnly : readOnlyMemory (sourceFunctionBody Guest.guestFn_htab_hash) = true := by
  rw [source_hash_scoped_body]; decide

/-- A declared `htab_hash` call whose arguments are words, with key length below
2^62, costs key_len / 8 + 9 plus its continuation, in every outcome; the
continuation runs with memory, addresses, endianness, globals and code of the
caller. -/
theorem runBounded_htabHash_decCall {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS)
    (pointerArgument lengthArgument : ExpHOL 64) (continuation : ProgHOL 64) (pointer keyLength : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [pointerArgument,lengthArgument] = some [.val (.word pointer),.val (.word keyLength)])
    (small : keyLength.toNat < 2 ^ 62) {tailCost : Nat}
    (budget : keyLength.toNat / 8 + 8 + 1 + tailCost ≤ state.clock)
    (tail : ∀ value (post : PanSemStateFiniteExact 64 F), post.code = state.code → post.memory = state.memory →
      post.memaddrs = state.memaddrs → post.be = state.be → post.globals = state.globals → tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite name value {post with locals := state.locals}) continuation tailCost) :
    RunBounded state (.decCall name .one (ofString "htab_hash") [pointerArgument,lengthArgument] continuation)
      (keyLength.toNat / 8 + 8 + 1 + tailCost) := by
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htab_hash") =
      some ([(ofString "p",.one),(ofString "key_len",.one)],sourceFunctionBody Guest.guestFn_htab_hash,.one) := by
    rw [code]; exact originalRuntimeCode_hash_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_hash") (ofString "p") (ofString "key_len")
    (sourceFunctionBody Guest.guestFn_htab_hash) pointer keyLength (by decide) installed] at lookup
  cases lookup
  constructor
  · refine evaluate_htabHash_body_bounded _ (by exact code) keyLength ?_ small ?_
    · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · change _ ≤ state.clock - 1; omega
  · intro value post run tc
    have meta' := evaluateHOLFiniteState_metadata
      (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
        (ofString "key_len",.val (.word keyLength)))) (sourceFunctionBody Guest.guestFn_htab_hash)
    have memory := evaluate_readOnly_memory _ htabHash_readOnly
      (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
        (ofString "key_len",.val (.word keyLength))))
    have globals := evaluate_readOnly_globals _ htabHash_readOnly
      (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
        (ofString "key_len",.val (.word keyLength))))
    rw [run] at meta' memory globals
    exact tail value post meta'.1 memory meta'.2.1 meta'.2.2.1 globals tc

#print axioms runBounded_htabHash_decCall
end InitECandidate.Runtime
