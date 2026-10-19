import InitECandidate.Runtime.StatelessMiddleWitnessHeaderOrigin
import InitECandidate.Runtime.WitnessArrayLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- All three original witness-list decoders and six record stores return
linked readable state, code and header arrays, retaining their size/heap bounds. -/
theorem stateless_first_witness_header_origin {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (P L WP WL W1 W2 S H : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atWP : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (atWL : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (atW1 : s.locals.lookup (ofString "w1") = some (.val (.word W1)))
    (atW2 : s.locals.lookup (ofString "w2") = some (.val (.word W2)))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) statelessFirstWitnessArguments =
      some [.val (.word P),.val (.word L),.val (.word (9223372036854775807#64)),.val (.word (1024#64))])
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2^64)
    (ordered : W1.toNat ≤ W2.toNat) (lastInside : W2.toNat ≤ WL.toNat)
    (witnessFits : WP.toNat + WL.toNat < 2^64)
    (run : evaluateHOLFiniteState s (statelessAt 39) = (some (.returned v),post)) :
    ∃ array count codes codeCount headers headerCount finalHeap : BitVec 64,
      v = .val (.word S) ∧
      WitnessArrayLinked post S 40 48 array count P L finalHeap ∧
      WitnessArrayLinked post S 56 64 codes codeCount (WP + W1) (W2 - W1) finalHeap ∧
      WitnessArrayLinked post S 72 80 headers headerCount (WP + W2) (WL - W2) finalHeap ∧
      (count = 0 ∨ array = H) ∧ (codeCount = 0 ∨ S.toNat + 88 ≤ codes.toNat) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ H.toNat ≤ finalHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → S.toNat + 88 ≤ w.toNat → post.memory w = s.memory w) ∧
      (headerCount = 0 ∨ S.toNat + 88 ≤ headers.toNat) := by
  have metadata := evaluateHOLFiniteState_metadata s (statelessAt 39)
  rw [run] at metadata
  have postDomain : post.memaddrs = s.memaddrs := metadata.2.1
  rw [source_stateless_first_witness] at run
  obtain ⟨ready,output,array,count,locals,atPair,installed,domain,decoded,countLe,origin,
    ⟨decodedHeap,decodedBinding,extent⟩,frame,⟨nextHeap,nextBinding,growth,cap,al,other⟩,tail,postGlobals,postMemory⟩ :=
    ret_bytesListDecl_input_frame s post (ofString "st0") statelessFirstWitnessArguments (statelessAt 40)
      P L 9223372036854775807 1024 H v code args heap capped aligned inputFits run
  have sameHeap : decodedHeap = nextHeap := by simpa using decodedBinding.symm.trans nextBinding
  rw [sameHeap] at extent
  have readySi := (locals _ (by decide)).trans atSi
  have stores : evaluateHOLFiniteState ready (witnessPairStores (ofString "st0") 40 48 (statelessAt 42)) =
      (some (.returned v),output) := by rw [← source_witness_pair_stores.1]; exact tail
  obtain ⟨next,middleRun,nextLocals,nextGlobals,nextDomain,nextCode,dom40,dom48,cell40,cell48,kept⟩ :=
    witness_pair_stores_returned ready output (ofString "st0") (40#64) (48#64) S array count (statelessAt 42) v readySi atPair (by decide) stores
  have localFrame (name : MlS) (different : name ≠ ofString "st0") : next.locals.lookup name = s.locals.lookup name := by
    rw [nextLocals]; exact locals name different
  have argsMiddle : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a)) statelessMiddleWitnessArguments =
      some [.val (.word (WP + W1)),.val (.word (W2 - W1)),.val (.word (9223372036854775807#64)),.val (.word (65536#64))] := by
    have wp := (localFrame _ (by decide)).trans atWP
    have w1 := (localFrame _ (by decide)).trans atW1
    have w2 := (localFrame _ (by decide)).trans atW2
    rw [evalListHOLFinite_eq_toExact]
    simp [statelessMiddleWitnessArguments,evalListHOLExact,evalHOLExact,wp,w1,w2,wordOpHOL,wordOp,valueIsWord,valueWord]
  have middleFits : (WP + W1).toNat + (W2 - W1).toNat < 2^64 := by
    rw [BitVec.toNat_add_of_lt (by omega),BitVec.toNat_sub_of_le (BitVec.le_def.mpr ordered)]
    omega
  obtain ⟨codes,codeCount,headers,headerCount,finalHeap,valueEq,d56,d64,c56,c64,d72,d80,c72,c80,
    codesDecoded,codesCount,codesOrigin,headersDecoded,headersCount,finalBinding,finalCap,finalAlign,finalGrowth,
    codesExtent,headersExtent,middleGlobals,middleFrame,middleFullFrame,headerOrigin⟩ :=
    stateless_middle_witness_header_origin next output (WP + W1) (W2 - W1) WP WL W2 S nextHeap v
      (nextCode.trans (installed.trans code)) ((localFrame _ (by decide)).trans atSi)
      ((localFrame _ (by decide)).trans atWP) ((localFrame _ (by decide)).trans atWL)
      ((localFrame _ (by decide)).trans atW2) argsMiddle (by rw [nextGlobals]; exact nextBinding)
      cap al (by omega) middleFits lastInside witnessFits middleRun
  have outputDomain : output.memaddrs = next.memaddrs := by
    have meta' := evaluateHOLFiniteState_metadata next (statelessAt 42)
    rw [middleRun] at meta'; exact meta'.2.1
  have postOutputDomain : post.memaddrs = output.memaddrs :=
    postDomain.trans (outputDomain.trans (nextDomain.trans domain)).symm
  have decodedNext : RlpSliceInputPrefix next array P L count.toNat := by
    apply decoded.after_pair_stores ready next array count P L (S + (40#64)) (S + (48#64))
      (by omega) nextDomain ?_ kept
    rcases origin with empty | same
    · exact Or.inl empty
    · right
      rw [same,word_add_toNat S 40 (by omega),word_add_toNat S 48 (by omega)]; omega
  have decodedOutput : RlpSliceInputPrefix output array P L count.toNat := by
    rcases origin with empty | same
    · subst count; exact rlpSliceInputPrefix_empty output array P L
    · apply decodedNext.after_memory_between next output array count P L nextHeap (S.toNat + 88)
        (by rw [same]; exact recordBefore) extent outputDomain middleFrame
  have unchanged (off : BitVec 64) (small : off.toNat < 56) : output.memory (S + off) = next.memory (S + off) := by
    apply middleFullFrame (S + off) (by rw [BitVec.toNat_add_of_lt (by omega)]; omega)
    all_goals intro e; have eq := congrArg BitVec.toNat (add_left_cancel e); simp at eq; omega
  have linkedState : WitnessArrayLinked output S 40 48 array count P L finalHeap :=
    ⟨by rw [outputDomain]; exact dom40,by rw [outputDomain]; exact dom48,
      (unchanged _ (by decide)).trans cell40,(unchanged _ (by decide)).trans cell48,decodedOutput,countLe,by omega⟩
  have linkedCodes : WitnessArrayLinked output S 56 64 codes codeCount (WP + W1) (W2 - W1) finalHeap :=
    ⟨d56,d64,c56,c64,codesDecoded,codesCount,codesExtent⟩
  have linkedHeaders : WitnessArrayLinked output S 72 80 headers headerCount (WP + W2) (WL - W2) finalHeap :=
    ⟨d72,d80,c72,c80,headersDecoded,headersCount,headersExtent⟩
  refine ⟨array,count,codes,codeCount,headers,headerCount,finalHeap,valueEq,
    linkedState.after_frame output post _ _ _ _ _ _ _ _ postOutputDomain postMemory,
    linkedCodes.after_frame output post _ _ _ _ _ _ _ _ postOutputDomain postMemory,
    linkedHeaders.after_frame output post _ _ _ _ _ _ _ _ postOutputDomain postMemory,origin,?_,?_,finalCap,finalAlign,(by omega),?_,?_,headerOrigin⟩
  · rcases codesOrigin with empty | same
    · exact Or.inl empty
    · right; rw [same]; omega
  · rw [postGlobals]; exact finalBinding
  · intro name different
    rw [postGlobals,middleGlobals name different,nextGlobals]; exact other name different
  · intro w below above
    rw [postMemory,middleFrame w (by omega) above]
    apply (kept w ?_ ?_).trans (frame w below)
    · intro e; rw [e,word_add_toNat S 40 (by omega)] at above; omega
    · intro e; rw [e,word_add_toNat S 48 (by omega)] at above; omega

#print axioms stateless_first_witness_header_origin
end InitECandidate.Runtime
