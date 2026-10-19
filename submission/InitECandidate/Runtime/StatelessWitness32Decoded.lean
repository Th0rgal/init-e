import InitECandidate.Runtime.StatelessWitness35Decoded
import InitECandidate.Runtime.StatelessWitnessSetupRun
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The complete original witness suffix, including its actual three-iteration
setup loop, returns linked state/code/header arrays and keeps earlier input
memory above the stateless-input record. -/
theorem stateless_witness32_decoded {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (WP WL S H offsets : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atWP : s.locals.lookup (ofString "wp") = some (.val (.word WP)))
    (atWL : s.locals.lookup (ofString "wlen") = some (.val (.word WL)))
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (witnessFits : WP.toNat + WL.toNat < 2^64)
    (scratchBefore : offsets.toNat + 24 ≤ S.toNat)
    (run : evaluateHOLFiniteState s (statelessAt 32) = (some (.returned v),post)) :
    ∃ middle last array count codes codeCount headers headerCount finalHeap : BitVec 64,
      12 ≤ middle.toNat ∧ middle.toNat ≤ last.toNat ∧ last.toNat ≤ WL.toNat ∧ v = .val (.word S) ∧
      WitnessArrayLinked post S 40 48 array count (WP + (12#64)) (middle - (12#64)) finalHeap ∧
      WitnessArrayLinked post S 56 64 codes codeCount (WP + middle) (last - middle) finalHeap ∧
      WitnessArrayLinked post S 72 80 headers headerCount (WP + last) (WL - last) finalHeap ∧
      (count = 0 ∨ array = H) ∧ (codeCount = 0 ∨ S.toNat + 88 ≤ codes.toNat) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧ H.toNat ≤ finalHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → S.toNat + 88 ≤ w.toNat → post.memory w = s.memory w) := by
  rcases evaluate_stateless_witness_setup s WL offsets code atWL atOffsets with ⟨entry,W0,W1,W2,valid,setup⟩ | aborted
  · rw [setup] at run
    obtain ⟨_,_,others,entryGlobals,entryDomain,entryCode,_,_,_,_,_,_,_,_,entryMemory⟩ := valid
    cases evaluated : evaluateHOLFiniteState entry (statelessAt 35) with
    | mk result output =>
      rw [evaluated] at run
      obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
      dsimp only at resultEq postEq
      subst resultEq
      obtain ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,inside,valueEq,
        stateLinked,codesLinked,headersLinked,origin,codesOrigin,finalBinding,cap,al,growth,other,frame⟩ :=
        stateless_witness35_decoded entry output WP WL S H offsets v (entryCode.trans code)
          ((others _ (by decide)).trans atSi) ((others _ (by decide)).trans atWP) ((others _ (by decide)).trans atWL)
          (by rw [entryGlobals]; exact atOffsets) (by rw [entryGlobals]; exact heap)
          capped aligned recordBefore witnessFits evaluated
      have memory : post.memory = output.memory := by rw [← postEq]
      have globals : post.globals = output.globals := by rw [← postEq]
      have domain : post.memaddrs = output.memaddrs := by rw [← postEq]
      refine ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,inside,valueEq,
        stateLinked.after_frame output post _ _ _ _ _ _ _ _ domain memory,
        codesLinked.after_frame output post _ _ _ _ _ _ _ _ domain memory,
        headersLinked.after_frame output post _ _ _ _ _ _ _ _ domain memory,origin,codesOrigin,?_,cap,al,growth,?_,?_⟩
      · rw [globals]; exact finalBinding
      · intro name different
        rw [globals,other name different,entryGlobals]
      · intro w below above
        rw [memory,frame w below above,entryMemory]
        have h0 : w ≠ offsets := by intro e; rw [e] at above; omega
        have h8 : w ≠ offsets + 8 := by
          change w ≠ offsets + (8#64)
          intro e; rw [e,word_add_toNat offsets 8 (by omega)] at above; omega
        have h16 : w ≠ offsets + 16 := by
          change w ≠ offsets + (16#64)
          intro e; rw [e,word_add_toNat offsets 16 (by omega)] at above; omega
        simp only [wmem,if_neg h16,if_neg h8,if_neg h0]
  · obtain ⟨result,ran,noReturn,spent,remaining,noTimeout⟩ := aborted
    rw [run] at ran
    exact False.elim (noReturn v (Option.some.inj ran).symm)

#print axioms stateless_witness32_decoded
end InitECandidate.Runtime
