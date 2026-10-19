import InitECandidate.Runtime.StatelessWitness28Decoded
import InitECandidate.Runtime.StatelessHashRequestWitnessLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The actual hash-count validation and outer record stores lead through
request decoding to the linked three-list witness result. -/
theorem stateless_witness24_decoded {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (NP NL OVH ORQ P L OW S H offsets : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (atNP : s.locals.lookup (ofString "np") = some (.val (.word NP)))
    (atNL : s.locals.lookup (ofString "nlen") = some (.val (.word NL)))
    (atOVH : s.locals.lookup (ofString "o_vh") = some (.val (.word OVH)))
    (atORQ : s.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)))
    (atP : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (atL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (atOW : s.locals.lookup (ofString "o_wit") = some (.val (.word OW)))
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2^64) (inside : OW.toNat ≤ L.toNat)
    (scratchBefore : offsets.toNat + 40 ≤ S.toNat)
    (run : evaluateHOLFiniteState s (statelessAt 24) = (some (.returned v),post)) :
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
  have run' : evaluateHOLFiniteState s (reqCount "nvh" "o_rq" "o_vh" 32 (statelessAt 25)) = (some (.returned v), post) := by
    rw [← run, source_stateless_hash_count]; rfl
  obtain ⟨mod, t1, out1, ⟨m1, g1, d1, c1, k1, n1⟩, r1, pm1, pg1, _⟩ :=
    reqCount_returned s post "nvh" "o_rq" "o_vh" 32 (statelessAt 25) ORQ OVH v atORQ atOVH code (by decide) run'
  have nv : ∀ n : String, n ∈ ["np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit", "si"] →
      ofString n ≠ ofString "nvh" := by
    intro n hn; simp at hn; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide_cbv
  have t1np := (k1 _ (nv "np" (by simp))).trans atNP
  have t1nlen := (k1 _ (nv "nlen" (by simp))).trans atNL
  have t1ovh := (k1 _ (nv "o_vh" (by simp))).trans atOVH
  have t1orq := (k1 _ (nv "o_rq" (by simp))).trans atORQ
  have t1p := (k1 _ (nv "p" (by simp))).trans atP
  have t1len := (k1 _ (nv "len" (by simp))).trans atL
  have t1ow := (k1 _ (nv "o_wit" (by simp))).trans atOW
  have t1si := (k1 _ (nv "si" (by simp))).trans atSi
  obtain ⟨a25, a26, a27⟩ := source_stateless_hash_stores_exact
  rw [a25] at r1
  obtain ⟨dom8, r2⟩ := seqStore_returned_exact t1 out1 _ _ _ (S + 8) (NP + OVH) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, evalListHOLExact, t1np, t1ovh, wordOpHOL, wordOp, valueIsWord, valueWord]) r1
  rw [a26] at r2
  obtain ⟨dom16, r3⟩ := seqStore_returned_exact _ out1 _ _ _ (S + 16) ((ORQ - OVH) / 32) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, n1]) r2
  rw [a27] at r3
  obtain ⟨dom24, r4⟩ := seqStore_returned_exact _ out1 _ _ _ (S + 24) (NP + 8) v
    (by simp [evalHOLExact, evalListHOLExact, t1si, wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, evalListHOLExact, t1np, wordOpHOL, wordOp, valueIsWord, valueWord]) r3
  generalize ht4 : ({({({t1 with memory := wmem t1.memory (S + 8) (NP + OVH)} : PanSemStateFiniteExact 64 F) with
    memory := wmem (wmem t1.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)} : PanSemStateFiniteExact 64 F) with
    memory := wmem (wmem (wmem t1.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)) (S + 24) (NP + 8)} :
      PanSemStateFiniteExact 64 F) = t4 at r4
  have t4l : t4.locals = t1.locals := by rw [← ht4]
  have t4g : t4.globals = s.globals := by rw [← ht4]; exact g1
  have t4c : t4.code = originalRuntimeCode := by rw [← ht4]; exact c1.trans code
  have t4m : t4.memory = wmem (wmem (wmem s.memory (S + 8) (NP + OVH)) (S + 16) ((ORQ - OVH) / 32)) (S + 24) (NP + 8) := by
    rw [← ht4, m1]
  obtain ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked,codesLinked,headersLinked,origin,codesOrigin,finalBinding,cap,al,growth,other,frame⟩ :=
    stateless_witness28_decoded t4 out1 NP NL ORQ P L OW S H offsets v t4c
      (by rw [t4l]; exact t1si) (by rw [t4l]; exact t1np) (by rw [t4l]; exact t1nlen)
      (by rw [t4l]; exact t1orq) (by rw [t4l]; exact t1p) (by rw [t4l]; exact t1len)
      (by rw [t4l]; exact t1ow) (by rw [t4g]; exact atOffsets) (by rw [t4g]; exact heap)
      capped aligned recordBefore inputFits inside scratchBefore r4
  have metadata := evaluateHOLFiniteState_metadata s (statelessAt 24)
  rw [run] at metadata
  have outMetadata := evaluateHOLFiniteState_metadata t4 (statelessAt 28)
  rw [r4] at outMetadata
  have domain : post.memaddrs = out1.memaddrs := by
    rw [metadata.2.1,outMetadata.2.1,← ht4,d1]
  refine ⟨middle,last,array,count,codes,codeCount,headers,headerCount,finalHeap,lower,ordered,bound,valueEq,
    stateLinked.after_frame out1 post _ _ _ _ _ _ _ _ domain pm1,
    codesLinked.after_frame out1 post _ _ _ _ _ _ _ _ domain pm1,
    headersLinked.after_frame out1 post _ _ _ _ _ _ _ _ domain pm1,origin,codesOrigin,?_,cap,al,growth,?_,?_⟩
  · rw [pg1]; exact finalBinding
  · intro name different
    rw [pg1,other name different,t4g]
  · intro w below above
    rw [pm1,frame w below above,t4m]
    have separate (off : Nat) (small : off < 88) : w ≠ S + BitVec.ofNat 64 off := by
      intro equal
      rw [equal,word_add_toNat S off (by omega)] at above
      omega
    have h24 : w ≠ S + 24 := separate 24 (by decide)
    have h16 : w ≠ S + 16 := separate 16 (by decide)
    have h8 : w ≠ S + 8 := separate 8 (by decide)
    simp only [wmem,if_neg h24,if_neg h16,if_neg h8]

#print axioms stateless_witness24_decoded
end InitECandidate.Runtime
