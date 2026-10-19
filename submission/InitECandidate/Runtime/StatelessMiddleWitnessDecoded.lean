import InitECandidate.Runtime.StatelessLastWitnessDecoded
import InitECandidate.Runtime.RlpSliceInputPrefixBetween
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The original code-list decoder and remaining header-list suffix return
both linked readable arrays; later decoding retains the earlier code array. -/
theorem stateless_middle_witness_decoded {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (P L WP WL W2 S H : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atWP : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (atWL : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (atW2 : s.locals.lookup (ofString "w2") = some (.val (.word W2)))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) statelessMiddleWitnessArguments =
      some [.val (.word P),.val (.word L),.val (.word (9223372036854775807#64)),.val (.word (65536#64))])
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2^64)
    (lastInside : W2.toNat ≤ WL.toNat) (witnessFits : WP.toNat + WL.toNat < 2^64)
    (run : evaluateHOLFiniteState s (statelessAt 42) = (some (.returned v),post)) :
    ∃ array count headers headerCount finalHeap : BitVec 64,
      v = .val (.word S) ∧
      post.memaddrs (S + (56#64)) ∧ post.memaddrs (S + (64#64)) ∧
      post.memory (S + (56#64)) = .word array ∧ post.memory (S + (64#64)) = .word count ∧
      post.memaddrs (S + (72#64)) ∧ post.memaddrs (S + (80#64)) ∧
      post.memory (S + (72#64)) = .word headers ∧ post.memory (S + (80#64)) = .word headerCount ∧
      RlpSliceInputPrefix post array P L count.toNat ∧ count.toNat ≤ L.toNat / 4 ∧ (count = 0 ∨ array = H) ∧
      RlpSliceInputPrefix post headers (WP + W2) (WL - W2) headerCount.toNat ∧
      headerCount.toNat ≤ (WL - W2).toNat / 4 ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ H.toNat ≤ finalHeap.toNat ∧
      array.toNat + count.toNat * 16 ≤ finalHeap.toNat ∧ headers.toNat + headerCount.toNat * 16 ≤ finalHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → S.toNat + 88 ≤ w.toNat → post.memory w = s.memory w) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → w ≠ S + (56#64) → w ≠ S + (64#64) →
        w ≠ S + (72#64) → w ≠ S + (80#64) → post.memory w = s.memory w) := by
  have metadata := evaluateHOLFiniteState_metadata s (statelessAt 42)
  rw [run] at metadata
  have postDomain : post.memaddrs = s.memaddrs := metadata.2.1
  rw [source_stateless_middle_witness] at run
  obtain ⟨ready,output,array,count,locals,atPair,installed,domain,decoded,countLe,origin,
    ⟨decodedHeap,decodedBinding,extent⟩,frame,⟨nextHeap,nextBinding,growth,cap,al,other⟩,tail,postGlobals,postMemory⟩ :=
    ret_bytesListDecl_input_frame s post (ofString "cd") statelessMiddleWitnessArguments (statelessAt 43)
      P L 9223372036854775807 65536 H v code args heap capped aligned inputFits run
  have sameHeap : decodedHeap = nextHeap := by simpa using decodedBinding.symm.trans nextBinding
  rw [sameHeap] at extent
  have readySi := (locals _ (by decide)).trans atSi
  have stores : evaluateHOLFiniteState ready (witnessPairStores (ofString "cd") 56 64 (statelessAt 45)) =
      (some (.returned v),output) := by rw [← source_witness_pair_stores.2.1]; exact tail
  obtain ⟨next,lastRun,nextLocals,nextGlobals,nextDomain,nextCode,dom56,dom64,cell56,cell64,kept⟩ :=
    witness_pair_stores_returned ready output (ofString "cd") (56#64) (64#64) S array count (statelessAt 45) v readySi atPair (by decide) stores
  have localFrame (name : MlS) (different : name ≠ ofString "cd") : next.locals.lookup name = s.locals.lookup name := by
    rw [nextLocals]; exact locals name different
  have argsLast : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a)) statelessLastWitnessArguments =
      some [.val (.word (WP + W2)),.val (.word (WL - W2)),.val (.word (256#64)),.val (.word (1024#64))] := by
    have wp := (localFrame _ (by decide)).trans atWP
    have wl := (localFrame _ (by decide)).trans atWL
    have w2 := (localFrame _ (by decide)).trans atW2
    rw [evalListHOLFinite_eq_toExact]
    simp [statelessLastWitnessArguments,evalListHOLExact,evalHOLExact,wp,wl,w2,wordOpHOL,wordOp,valueIsWord,valueWord]
  have lastFits : (WP + W2).toNat + (WL - W2).toNat < 2^64 := by
    rw [BitVec.toNat_add_of_lt (by omega),BitVec.toNat_sub_of_le (BitVec.le_def.mpr lastInside)]
    omega
  obtain ⟨headers,headerCount,finalHeap,valueEq,h72,h80,c72,c80,lastDecoded,lastCount,lastOrigin,
    finalBinding,finalCap,finalAlign,finalGrowth,lastExtent,lastGlobals,lastFrame,lastFullFrame⟩ :=
    stateless_last_witness_decoded next output (WP + W2) (WL - W2) S nextHeap v
      (nextCode.trans (installed.trans code)) ((localFrame _ (by decide)).trans atSi) argsLast
      (by rw [nextGlobals]; exact nextBinding) cap al (by omega) lastFits lastRun
  have outputDomain : output.memaddrs = next.memaddrs := by
    have meta' := evaluateHOLFiniteState_metadata next (statelessAt 45)
    rw [lastRun] at meta'; exact meta'.2.1
  have postOutputDomain : post.memaddrs = output.memaddrs :=
    postDomain.trans (outputDomain.trans (nextDomain.trans domain)).symm
  have decodedNext : RlpSliceInputPrefix next array P L count.toNat := by
    apply decoded.after_pair_stores ready next array count P L (S + (56#64)) (S + (64#64))
      (by omega) nextDomain ?_ kept
    rcases origin with empty | same
    · exact Or.inl empty
    · right
      rw [same,word_add_toNat S 56 (by omega),word_add_toNat S 64 (by omega)]; omega
  have decodedOutput : RlpSliceInputPrefix output array P L count.toNat := by
    rcases origin with empty | same
    · subst count; exact rlpSliceInputPrefix_empty output array P L
    · apply decodedNext.after_memory_between next output array count P L nextHeap (S.toNat + 88)
        (by rw [same]; exact recordBefore) extent outputDomain lastFrame
  have out56 := lastFullFrame (S + (56#64)) (by rw [word_add_toNat S 56 (by omega)]; omega)
    (by intro e; have := add_left_cancel e; contradiction) (by intro e; have := add_left_cancel e; contradiction)
  have out64 := lastFullFrame (S + (64#64)) (by rw [word_add_toNat S 64 (by omega)]; omega)
    (by intro e; have := add_left_cancel e; contradiction) (by intro e; have := add_left_cancel e; contradiction)
  refine ⟨array,count,headers,headerCount,finalHeap,valueEq,?_,?_,?_,?_,?_,?_,?_,?_,?_,countLe,origin,?_,lastCount,?_,
    finalCap,finalAlign,(by omega),(by omega),lastExtent,?_,?_,?_⟩
  · rw [postOutputDomain,outputDomain]; exact dom56
  · rw [postOutputDomain,outputDomain]; exact dom64
  · rw [postMemory,out56]; exact cell56
  · rw [postMemory,out64]; exact cell64
  · rw [postOutputDomain]; exact h72
  · rw [postOutputDomain]; exact h80
  · rw [postMemory]; exact c72
  · rw [postMemory]; exact c80
  · intro j inside
    obtain ⟨src,len,entry⟩ := decodedOutput j inside
    exact ⟨src,len,entry.after_frame output post array j src len P L postOutputDomain (congrFun postMemory _) (congrFun postMemory _)⟩
  · intro j inside
    obtain ⟨src,len,entry⟩ := lastDecoded j inside
    exact ⟨src,len,entry.after_frame output post headers j src len (WP + W2) (WL - W2)
      postOutputDomain (congrFun postMemory _) (congrFun postMemory _)⟩
  · rw [postGlobals]; exact finalBinding
  · intro name different
    rw [postGlobals,lastGlobals name different,nextGlobals]; exact other name different
  · intro w below above
    rw [postMemory,lastFrame w (by omega) above]
    apply (kept w ?_ ?_).trans (frame w below)
    · intro e; rw [e,word_add_toNat S 56 (by omega)] at above; omega
    · intro e; rw [e,word_add_toNat S 64 (by omega)] at above; omega

  · intro w below h56 h64 h72 h80
    rw [postMemory,lastFullFrame w (by omega) h72 h80]
    exact (kept w h56 h64).trans (frame w below)

#print axioms stateless_middle_witness_decoded
end InitECandidate.Runtime
