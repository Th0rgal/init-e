import InitECandidate.Runtime.StatelessWitness24Decoded
import InitECandidate.Runtime.StatelessPayloadSuffixReturnedCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Original payload decoding and its record store preserve the premises for
request/witness decoding, yielding all three linked witness arrays. -/
theorem stateless_witness22_decoded {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (NP NL OPL OVH ORQ P L OW S H offsets : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atNP : s.locals.lookup (ofString "np") = some (.val (.word NP)))
    (atNL : s.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (atOPL : s.locals.lookup (ofString "o_pl") = some (.val (.word OPL)))
    (atOVH : s.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (atORQ : s.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (atP : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (atL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (atOW : s.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 96 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2^64) (inside : OW.toNat ≤ L.toNat)
    (scratchBefore : offsets.toNat + 40 ≤ S.toNat)
    (heapArena : ∀ a : BitVec 64, a.toNat % 8 = 0 → H.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (scratchDom : s.memaddrs (offsets + 0) ∧ s.memaddrs (offsets + 8) ∧ s.memaddrs (offsets + 16) ∧ s.memaddrs (offsets + 24))
    (payloadFits : (NP + OPL).toNat + (OVH - OPL).toNat < 2^64)
    (run : evaluateHOLFiniteState s (statelessAt 22) = (some (.returned v),post)) :
    ∃ middle last array count codes codeCount headers headerCount finalHeap : BitVec 64,
      12 ≤ middle.toNat ∧ middle.toNat ≤ last.toNat ∧ last.toNat ≤ (L - OW).toNat ∧ v = .val (.word S) ∧
      WitnessArrayLinked post S 40 48 array count ((P + OW) + (12#64)) (middle - (12#64)) finalHeap ∧
      WitnessArrayLinked post S 56 64 codes codeCount ((P + OW) + middle) (last - middle) finalHeap ∧
      WitnessArrayLinked post S 72 80 headers headerCount ((P + OW) + last) ((L - OW) - last) finalHeap ∧
      (count = 0 ∨ S.toNat + 88 ≤ array.toNat) ∧ (codeCount = 0 ∨ S.toNat + 88 ≤ codes.toNat) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ H.toNat ≤ finalHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → S.toNat + 88 ≤ w.toNat → post.memory w = s.memory w) := by
  rw [source_stateless_payload_call] at run
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) statelessPayloadArguments =
      some [.val (.word (NP + OPL)),.val (.word (OVH - OPL))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [statelessPayloadArguments,evalListHOLExact,evalHOLExact,atNP,atOPL,atOVH,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨ready,output,nextHeap,payloadArray,payloadCount,_,_,_,_,_,_,locals,atPayload,installed,readyDomain,
    _,_,_,nextBinding,cap,al,growth,other,frame,tail,postGlobals,postMemory,postDomain⟩ :=
    ret_payloadDecl_cells s post (ofString "pl") statelessPayloadArguments (statelessAt 23)
      (NP + OPL) (OVH - OPL) offsets H v code args atOffsets heap capped aligned heapArena scratchDom
      (by omega) payloadFits run
  have si := (locals _ (by decide)).trans atSi
  rw [source_stateless_payload_store] at tail
  unfold statelessPayloadStore at tail
  obtain ⟨recordDomain,body⟩ := seqStore_returned_exact ready output _ _ _ (S + (0#64)) H v
    (by simp [evalHOLExact,evalListHOLExact,si,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atPayload]) tail
  let next : PanSemStateFiniteExact 64 F := {ready with memory := wmem ready.memory (S + (0#64)) H}
  obtain ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked,codesLinked,headersLinked,origin,codesOrigin,finalBinding,finalCap,finalAlign,finalGrowth,finalOther,finalFrame⟩ :=
    stateless_witness24_decoded next output NP NL OVH ORQ P L OW S nextHeap offsets v (installed.trans code) si
      ((locals _ (by decide)).trans atNP) ((locals _ (by decide)).trans atNL) ((locals _ (by decide)).trans atOVH)
      ((locals _ (by decide)).trans atORQ) ((locals _ (by decide)).trans atP) ((locals _ (by decide)).trans atL)
      ((locals _ (by decide)).trans atOW)
      (by change ready.globals.lookup _ = _; rw [other _ (by decide)]; exact atOffsets) nextBinding cap al
      (by omega) inputFits inside scratchBefore body
  refine ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked.after_frame output post _ _ _ _ _ _ _ _ postDomain postMemory,
    codesLinked.after_frame output post _ _ _ _ _ _ _ _ postDomain postMemory,
    headersLinked.after_frame output post _ _ _ _ _ _ _ _ postDomain postMemory,origin,codesOrigin,?_,finalCap,finalAlign,(by omega),?_,?_⟩
  · rw [postGlobals]; exact finalBinding
  · intro name different
    rw [postGlobals,finalOther name different]; exact other name different
  · intro w below above
    rw [postMemory,finalFrame w (by omega) above]
    have notRecord : w ≠ S + (0#64) := by intro e; simp only [BitVec.add_zero] at e; rw [e] at above; omega
    change (if w = S + (0#64) then HolWordLab.word H else ready.memory w) = s.memory w
    rw [if_neg notRecord]
    apply frame w below
    · intro e; rw [e] at above; omega
    · intro e; rw [e] at above
      change S.toNat + 88 ≤ (offsets + (8#64)).toNat at above
      rw [word_add_toNat offsets 8 (by omega)] at above; omega
    · intro e; rw [e] at above
      change S.toNat + 88 ≤ (offsets + (16#64)).toNat at above
      rw [word_add_toNat offsets 16 (by omega)] at above; omega
    · intro e; rw [e] at above
      change S.toNat + 88 ≤ (offsets + (24#64)).toNat at above
      rw [word_add_toNat offsets 24 (by omega)] at above; omega

#print axioms stateless_witness22_decoded
end InitECandidate.Runtime
