import InitECandidate.Runtime.StatelessWitnessLoadedEntry
import InitECandidate.Runtime.StatelessFirstWitnessHeaderOrigin
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The original witness check, offset loads, all three list decoders, record
stores and return establish linked readable witness arrays. Offset ordering
is discharged by the actual accepted check, not assumed at list entry. -/
theorem stateless_witness35_header_origin {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (WP WL S H offsets : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atWP : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (atWL : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (witnessFits : WP.toNat + WL.toNat < 2^64)
    (run : evaluateHOLFiniteState s (statelessAt 35) = (some (.returned v),post)) :
    ∃ middle last array count codes codeCount headers headerCount finalHeap : BitVec 64,
      12 ≤ middle.toNat ∧ middle.toNat ≤ last.toNat ∧ last.toNat ≤ WL.toNat ∧ v = .val (.word S) ∧
      WitnessArrayLinked post S 40 48 array count (WP + (12#64)) (middle - (12#64)) finalHeap ∧
      WitnessArrayLinked post S 56 64 codes codeCount (WP + middle) (last - middle) finalHeap ∧
      WitnessArrayLinked post S 72 80 headers headerCount (WP + last) (WL - last) finalHeap ∧
      (count = 0 ∨ array = H) ∧ (codeCount = 0 ∨ S.toNat + 88 ≤ codes.toNat) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ H.toNat ≤ finalHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → S.toNat + 88 ≤ w.toNat → post.memory w = s.memory w) ∧
      (headerCount = 0 ∨ S.toNat + 88 ≤ headers.toNat) := by
  obtain ⟨checkedState,tail,checkLocals,checkMemory,checkGlobals,checkDomain,checkCode,accepted⟩ :=
    stateless_witness_checked_entry s post offsets WL v code atOffsets atWL run
  have accepted' : SszCheckOffsetsReturned checkedState offsets 3 12 WL (.val (.word 0)) := by
    simpa only [SszCheckOffsetsReturned,SszOffsetOK,checkMemory,checkDomain] using accepted
  obtain ⟨ready,output,middle,last,body,w0,w1,w2,kept,memory,globals,domain,installed,postMemory,postGlobals,lower,ordered,inside⟩ :=
    stateless_witness_loaded_entry checkedState post offsets WL v (by rw [checkGlobals]; exact atOffsets) accepted' tail
  have localKeep (name : MlS) (n0 : name ≠ ofString "w0") (n1 : name ≠ ofString "w1") (n2 : name ≠ ofString "w2") :
      ready.locals.lookup name = s.locals.lookup name := by rw [kept name n0 n1 n2,checkLocals]
  have si := (localKeep _ (by decide) (by decide) (by decide)).trans atSi
  have wp := (localKeep _ (by decide) (by decide) (by decide)).trans atWP
  have wl := (localKeep _ (by decide) (by decide) (by decide)).trans atWL
  have args : evalListHOLFinite ready (h := fun a => Classical.propDecidable (ready.memaddrs a)) statelessFirstWitnessArguments =
      some [.val (.word (WP + (12#64))),.val (.word (middle - (12#64))),
        .val (.word (9223372036854775807#64)),.val (.word (1024#64))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [statelessFirstWitnessArguments,evalListHOLExact,evalHOLExact,wp,w0,w1,wordOpHOL,wordOp,valueIsWord,valueWord]
  have firstFits : (WP + (12#64)).toNat + (middle - (12#64)).toNat < 2^64 := by
    rw [BitVec.toNat_add_of_lt (by change WP.toNat + 12 < 2^64; omega),
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 12 ≤ middle.toNat; exact lower))]
    change WP.toNat + 12 + (middle.toNat - 12) < 2^64
    omega
  obtain ⟨array,count,codes,codeCount,headers,headerCount,finalHeap,valueEq,stateLinked,codesLinked,headersLinked,
    origin,codesOrigin,finalBinding,cap,al,growth,other,frame,headerOrigin⟩ :=
    stateless_first_witness_header_origin ready output (WP + (12#64)) (middle - (12#64)) WP WL middle last S H v
      (installed.trans (checkCode.trans code)) si wp wl w1 w2 args
      (by rw [globals,checkGlobals]; exact heap) capped aligned recordBefore firstFits ordered inside witnessFits body
  have metadata := evaluateHOLFiniteState_metadata s (statelessAt 35)
  rw [run] at metadata
  have outMetadata := evaluateHOLFiniteState_metadata ready (statelessAt 39)
  rw [body] at outMetadata
  have postOutputDomain : post.memaddrs = output.memaddrs :=
    metadata.2.1.trans (outMetadata.2.1.trans (domain.trans checkDomain)).symm
  refine ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,inside,valueEq,
    stateLinked.after_frame output post _ _ _ _ _ _ _ _ postOutputDomain postMemory,
    codesLinked.after_frame output post _ _ _ _ _ _ _ _ postOutputDomain postMemory,
    headersLinked.after_frame output post _ _ _ _ _ _ _ _ postOutputDomain postMemory,origin,codesOrigin,?_,cap,al,growth,?_,?_,headerOrigin⟩
  · rw [postGlobals]; exact finalBinding
  · intro name different
    rw [postGlobals,other name different,globals,checkGlobals]
  · intro w below above
    rw [postMemory,frame w below above,memory,checkMemory]

#print axioms stateless_witness35_header_origin
end InitECandidate.Runtime
