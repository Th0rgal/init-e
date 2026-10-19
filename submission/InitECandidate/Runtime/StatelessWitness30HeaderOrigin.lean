import InitECandidate.Runtime.StatelessWitness32HeaderOrigin
import InitECandidate.Runtime.StatelessWitnessEntryBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The full witness decoding suffix starts with its actual outer-input
subspan declarations; all three linked array contracts follow from execution. -/
theorem stateless_witness30_header_origin {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (P L OW S H offsets : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atP : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (atL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (atOW : s.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2^64) (inside : OW.toNat ≤ L.toNat)
    (scratchBefore : offsets.toNat + 24 ≤ S.toNat)
    (run : evaluateHOLFiniteState s (statelessAt 30) = (some (.returned v),post)) :
    ∃ middle last array count codes codeCount headers headerCount finalHeap : BitVec 64,
      12 ≤ middle.toNat ∧ middle.toNat ≤ last.toNat ∧ last.toNat ≤ (L - OW).toNat ∧ v = .val (.word S) ∧
      WitnessArrayLinked post S 40 48 array count ((P + OW) + (12#64)) (middle - (12#64)) finalHeap ∧
      WitnessArrayLinked post S 56 64 codes codeCount ((P + OW) + middle) (last - middle) finalHeap ∧
      WitnessArrayLinked post S 72 80 headers headerCount ((P + OW) + last) ((L - OW) - last) finalHeap ∧
      (count = 0 ∨ array = H) ∧ (codeCount = 0 ∨ S.toNat + 88 ≤ codes.toNat) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ H.toNat ≤ finalHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → S.toNat + 88 ≤ w.toNat → post.memory w = s.memory w) ∧
      (headerCount = 0 ∨ S.toNat + 88 ≤ headers.toNat) := by
  rw [source_stateless_witness_pointer] at run
  obtain ⟨pointerValue,pointerPost,pointerInit,lengthRun,pointerScope⟩ :=
    evaluate_dec_returned_scope s post (ofString "wp") .one _ _ v run
  have pEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "p"),.var .local (ofString "o_wit")]) = some (.val (.word (P + OW))) := by
    simp [evalHOLExact,evalListHOLExact,atP,atOW,wordOpHOL,wordOp,valueIsWord,valueWord]
  have pEq := Option.some.inj (pointerInit.symm.trans pEval)
  subst pEq
  let one := setVarHOLFinite (ofString "wp") (.val (.word (P + OW))) s
  rw [source_stateless_witness_length] at lengthRun
  obtain ⟨lengthValue,output,lengthInit,body,lengthScope⟩ :=
    evaluate_dec_returned_scope one pointerPost (ofString "wlen") .one _ _ v lengthRun
  have lEval : @evalHOLExact 64 F _ one.toExact (fun a => Classical.propDecidable (one.memaddrs a))
      (.op .sub [.var .local (ofString "len"),.var .local (ofString "o_wit")]) = some (.val (.word (L - OW))) := by
    simp (config := {decide := true}) [one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      evalHOLExact,evalListHOLExact,atL,atOW,wordOpHOL,wordOp,valueIsWord,valueWord]
  have lEq := Option.some.inj (lengthInit.symm.trans lEval)
  subst lEq
  let ready := setVarHOLFinite (ofString "wlen") (.val (.word (L - OW))) one
  have atWP : ready.locals.lookup (ofString "wp") = some (.val (.word (P + OW))) := by
    simp (config := {decide := true}) [ready,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atWL : ready.locals.lookup (ofString "wlen") = some (.val (.word (L - OW))) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atSi' : ready.locals.lookup (ofString "si") = some (.val (.word S)) := by
    simpa (config := {decide := true}) [ready,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSi
  have fits : (P + OW).toNat + (L - OW).toNat < 2^64 := by
    rw [BitVec.toNat_add_of_lt (by omega),BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)]
    omega
  obtain ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked,codesLinked,headersLinked,origin,codesOrigin,finalBinding,cap,al,growth,other,frame,headerOrigin⟩ :=
    stateless_witness32_header_origin ready output (P + OW) (L - OW) S H offsets v code atSi' atWP atWL atOffsets heap
      capped aligned recordBefore fits scratchBefore body
  have memory : post.memory = output.memory := by
    rw [pointerScope]; show pointerPost.memory = _; rw [lengthScope]
  have globals : post.globals = output.globals := by
    rw [pointerScope]; show pointerPost.globals = _; rw [lengthScope]
  have domain : post.memaddrs = output.memaddrs := by
    rw [pointerScope]; show pointerPost.memaddrs = _; rw [lengthScope]
  refine ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked.after_frame output post _ _ _ _ _ _ _ _ domain memory,
    codesLinked.after_frame output post _ _ _ _ _ _ _ _ domain memory,
    headersLinked.after_frame output post _ _ _ _ _ _ _ _ domain memory,origin,codesOrigin,?_,cap,al,growth,?_,?_,headerOrigin⟩
  · rw [globals]; exact finalBinding
  · intro name different
    rw [globals]; exact other name different
  · intro w below above
    rw [memory]; exact frame w below above

#print axioms stateless_witness30_header_origin
end InitECandidate.Runtime
