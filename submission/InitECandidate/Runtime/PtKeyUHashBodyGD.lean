import InitECandidate.Runtime.PtKeyUHashGD
import InitECandidate.Runtime.HashBodyWidths
import InitECandidate.Runtime.AlignedCellDomains
/-!
The complete source `htab_hash` body for 20/32/52-byte keys at any alignment.  The only memory premise is that every
key byte lies in an addressable aligned cell (`memaddrs (panByteAlignHOL (p + j))`, satisfiable in the actual
aligned-only domain); the aligned branch's word cells are derived from it (`aligned_word_domain_of_byte_domain`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

section ev
variable {F : Type}

/-- Byte cells of one hash word from the key's byte cells. -/
theorem kuDom (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (n : Nat)
    (bytes : ∀ j : Nat, j < n → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 j)))
    (w : KuW) (hw : (kuOff w.base).toNat + w.len ≤ n) :
    ∀ j : Nat, j < w.len → state.memaddrs (panByteAlignHOL (pointer + kuOff w.base + BitVec.ofNat 64 j)) := by
  intro j hj
  have hl : w.len ≤ 8 := by cases w <;> simp [KuW.len]
  have e : kuOff w.base + BitVec.ofNat 64 j = BitVec.ofNat 64 ((kuOff w.base).toNat + j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := (kuOff w.base).isLt
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
  rw [BitVec.add_assoc, e]
  exact bytes _ (by omega)

theorem eval_hash_unaligned_cond (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (unaligned : pointer.toNat % 8 ≠ 0) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      hashAlignmentCondition = some (.val (.word (0 : BitVec 64))) := by
  have mask : pointer &&& (7 : BitVec 64) ≠ 0 := by
    intro h
    apply unaligned
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_and] at this
    change pointer.toNat &&& (2^3 - 1) = 0 at this
    rwa [Nat.and_two_pow_sub_one_eq_mod] at this
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.var .local (ofString "p"),.const 7]) = some (.val (.word (pointer &&& 7))) := by
    simp [evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]
    show pointer &&& ((7 : BitVec 64) &&& 18446744073709551615#64) = pointer &&& 7
    congr 1
  unfold hashAlignmentCondition
  rw [evalHOLExact,loaded]
  simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
  exact mask

/-- Size-condition outcome for a key length `n`. -/
theorem eval_hashSize (state : PanSemStateFiniteExact 64 F) (n s : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word n))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (hashSizeCondition s) = some (.val (.word (if n = s then 1 else 0))) := by
  simp [hashSizeCondition,evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]

/-- The unaligned branch for one of the three supported widths. -/
theorem evaluate_hash_unaligned (state : PanSemStateFiniteExact 64 F) (pointer hash oldWord n : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word n)))
    (sup : n = 20 ∨ n = 32 ∨ n = 52)
    (bytes : ∀ j : Nat, j < n.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 j))) :
    ∃ value post, evaluateHOLFiniteState state hashUnalignedBody = (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have c20 := eval_hashSize state n 20 lengthLocal
  have c32 := eval_hashSize state n 32 lengthLocal
  have c52 := eval_hashSize state n 52 lengthLocal
  rw [source_hash_unaligned, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, c20]
  rcases sup with rfl | rfl | rfl
  · obtain ⟨v, post, run, fr⟩ := evaluate_kuChain [.w64 [], .w64 [8], .w32 [16]] state pointer hash oldWord
      pointerLocal hashLocal wordLocal (fun w hw => kuDom state pointer 20 bytes w (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> decide))
    refine ⟨v, post, ?_, fr⟩
    simp only [if_pos, show ¬(1 : BitVec 64) = 0 by decide, if_false]
    rw [show hashU20 = kuChain [.w64 [], .w64 [8], .w32 [16]] from rfl, run]
  · obtain ⟨v, post, run, fr⟩ := evaluate_kuChain [.w64 [], .w64 [8], .w64 [16], .w64 [24]] state pointer hash
      oldWord pointerLocal hashLocal wordLocal (fun w hw => kuDom state pointer 32 bytes w (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> decide))
    refine ⟨v, post, ?_, fr⟩
    simp only [show ¬((32 : BitVec 64) = 20) by decide, if_false, if_true, evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, c32]
    simp only [if_pos, show ¬(1 : BitVec 64) = 0 by decide, if_false]
    rw [show hashU32 = kuChain [.w64 [], .w64 [8], .w64 [16], .w64 [24]] from rfl, run]
  · obtain ⟨v, post, run, fr⟩ := evaluate_kuChain [.w64 [], .w64 [8], .w64 [16], .w64 [24], .w64 [32], .w64 [40],
      .w32 [48]] state pointer hash oldWord pointerLocal hashLocal wordLocal (fun w hw => kuDom state pointer 52 bytes w (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    refine ⟨v, post, ?_, fr⟩
    simp only [show ¬((52 : BitVec 64) = 20) by decide, if_false, if_true, evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, c32]
    simp only [show ¬((52 : BitVec 64) = 32) by decide, if_false, if_true, evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_ite, c52]
    simp only [if_pos, show ¬(1 : BitVec 64) = 0 by decide, if_false]
    exact run

end ev
#print axioms evaluate_hash_unaligned
end InitECandidate.Runtime
