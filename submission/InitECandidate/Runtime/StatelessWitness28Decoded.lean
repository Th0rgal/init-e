import InitECandidate.Runtime.StatelessWitness30Decoded
import InitECandidate.Runtime.StatelessRequestsDeclarationFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual request decoder and request-pointer store lead to the complete
witness-array contract, including preservation through request allocation. -/
theorem stateless_witness28_decoded {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (NP NL ORQ P L OW S H offsets : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atNP : s.locals.lookup (ofString "np") = some (.val (.word NP)))
    (atNL : s.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (atORQ : s.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (atP : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (atL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (atOW : s.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2^64) (inside : OW.toNat ≤ L.toNat)
    (scratchBefore : offsets.toNat + 40 ≤ S.toNat)
    (run : evaluateHOLFiniteState s (statelessAt 28) = (some (.returned v),post)) :
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
  rw [source_stateless_request_call] at run
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) statelessRequestArguments =
      some [.val (.word (NP + ORQ)),.val (.word (NL - ORQ))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [statelessRequestArguments,evalListHOLExact,evalHOLExact,atNP,atNL,atORQ,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨ready,output,locals,atRq,installed,readyDomain,frame,⟨nextHeap,nextBinding,growth,cap,al,other⟩,
    tail,postGlobals,postMemory,postDomain⟩ :=
    ret_requestsDecl_mem_domain s post (ofString "rq") statelessRequestArguments (statelessAt 29)
      (NP + ORQ) (NL - ORQ) H offsets v code args heap atOffsets capped run
  have si := (locals _ (by decide)).trans atSi
  rw [source_stateless_request_store] at tail
  unfold statelessRequestStore at tail
  obtain ⟨recordDomain,body⟩ := seqStore_returned_exact ready output _ _ _ (S + (32#64)) H v
    (by simp [evalHOLExact,evalListHOLExact,si,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atRq]) tail
  let next : PanSemStateFiniteExact 64 F := {ready with memory := wmem ready.memory (S + (32#64)) H}
  obtain ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked,codesLinked,headersLinked,origin,codesOrigin,finalBinding,finalCap,finalAlign,finalGrowth,finalOther,finalFrame⟩ :=
    stateless_witness30_decoded next output P L OW S nextHeap offsets v (installed.trans code) si
      ((locals _ (by decide)).trans atP) ((locals _ (by decide)).trans atL) ((locals _ (by decide)).trans atOW)
      (by change ready.globals.lookup _ = _; rw [other _ (by decide)]; exact atOffsets) nextBinding cap al
      (by omega) inputFits inside (by omega) body
  refine ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked.after_frame output post _ _ _ _ _ _ _ _ postDomain postMemory,
    codesLinked.after_frame output post _ _ _ _ _ _ _ _ postDomain postMemory,
    headersLinked.after_frame output post _ _ _ _ _ _ _ _ postDomain postMemory,?_,codesOrigin,?_,finalCap,finalAlign,(by omega),?_,?_⟩
  · rcases origin with empty | same
    · exact Or.inl empty
    · right; rw [same]; omega
  · rw [postGlobals]; exact finalBinding
  · intro name different
    rw [postGlobals,finalOther name different]; exact other name different
  · intro w below above
    rw [postMemory,finalFrame w (by omega) above]
    have notRecord : w ≠ S + (32#64) := by
      intro e; rw [e,word_add_toNat S 32 (by omega)] at above; omega
    change (if w = S + (32#64) then HolWordLab.word H else ready.memory w) = s.memory w
    rw [if_neg notRecord]
    apply frame w below
    intro k small equal
    have natural : (offsets + k * (8#64)).toNat = offsets.toNat + k.toNat * 8 :=
      word_mul_add_toNat offsets k (8#64) (by change offsets.toNat + k.toNat * 8 < 2^64; omega)
    change w = offsets + k * (8#64) at equal
    rw [equal,natural] at above
    omega

#print axioms stateless_witness28_decoded
end InitECandidate.Runtime
