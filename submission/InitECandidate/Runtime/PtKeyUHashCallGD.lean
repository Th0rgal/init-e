import InitECandidate.Runtime.PtKeyUHashBodyGD
/-!
The complete source `htab_hash` body for 20/32/52-byte keys at any alignment, from the key's byte cells alone.
The aligned branch reuses root's aligned evaluations with word cells derived from the byte cells.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

section ev
variable {F : Type}

/-- Word cells of an aligned key at the multiples of eight, from its byte cells. -/
theorem kuWordCells (state : PanSemStateFiniteExact 64 F) (pointer n : BitVec 64)
    (fits : pointer.toNat + n.toNat ≤ 33806089496) (aligned : pointer.toNat % 8 = 0)
    (bytes : ∀ j : Nat, j < n.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 j)))
    (offs : List Nat) (hoffs : ∀ o ∈ offs, o % 8 = 0 ∧ o < n.toNat) :
    ∀ o ∈ offs, state.memaddrs (pointer + BitVec.ofNat 64 o) := by
  intro o ho
  obtain ⟨a, b⟩ := hoffs o ho
  exact aligned_word_domain_of_byte_domain state pointer n fits bytes o b (by omega)

/-- Byte cells of the four-byte tail at `t`, from the key's byte cells. -/
theorem kuTailCells (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (n t : Nat) (ht : t + 4 ≤ n)
    (bytes : ∀ j : Nat, j < n → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 j))) :
    ∀ extra : BitVec 64, extra ∈ [0,1,2,3] →
      state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 t + extra)) := by
  intro extra he
  have hx : extra.toNat < 4 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  have e : BitVec.ofNat 64 t + extra = BitVec.ofNat 64 (t + extra.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.add_assoc, e]
  exact bytes _ (by omega)

/-- Complete original `htab_hash` body for a supported width at any key alignment. -/
theorem evaluate_source_hashK (state : PanSemStateFiniteExact 64 F) (pointer n : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "key_len") = some (.val (.word n)))
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (fits : pointer.toNat + n.toNat ≤ 33806089496)
    (bytes : ∀ j : Nat, j < n.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 j))) :
    ∃ value : BitVec 64, ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_hash) =
        (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let seeded := setVarHOLFinite (ofString "h") (.val (.word (14695981039346656037 : BitVec 64))) state
  let entered := setVarHOLFinite (ofString "w") (.val (.word (0 : BitVec 64))) seeded
  have hp : ofString "h" ≠ ofString "p" := by decide
  have wp : ofString "w" ≠ ofString "p" := by decide
  have hn : ofString "h" ≠ ofString "key_len" := by decide
  have wn : ofString "w" ≠ ofString "key_len" := by decide
  have wh : ofString "w" ≠ ofString "h" := by decide
  have p : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,wp] using pointerLocal
  have nl : entered.locals.lookup (ofString "key_len") = some (.val (.word n)) := by
    simpa [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn,wn] using lengthLocal
  have h : entered.locals.lookup (ofString "h") = some (.val (.word (14695981039346656037 : BitVec 64))) := by
    simp [entered,seeded,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,wh]
  have w : entered.locals.lookup (ofString "w") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eb : ∀ j : Nat, j < n.toNat → entered.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 j)) := bytes
  have selected : ∃ value : BitVec 64, ∃ post, evaluateHOLFiniteState entered
      (.seq (.ite hashAlignmentCondition hashAlignedBody hashUnalignedBody) hashAfterAlignment) =
        (some (.returned (.val (.word value))),post) ∧
      post.clock = entered.clock ∧ post.memory = entered.memory ∧ post.globals = entered.globals ∧
      post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
    by_cases al : pointer.toNat % 8 = 0
    · have cond := eval_hash_alignment entered pointer p al
      have run : ∃ value post, evaluateHOLFiniteState entered hashAlignedBody =
          (some (.returned (.val (.word value))),post) ∧
          post.clock = entered.clock ∧ post.memory = entered.memory ∧ post.globals = entered.globals ∧
          post.code = entered.code ∧ post.memaddrs = entered.memaddrs ∧ post.be = entered.be := by
        rcases sup with rfl | rfl | rfl
        · exact evaluate_hash_aligned20 entered pointer _ _ p h w nl
            (kuWordCells entered pointer 20 fits al eb [0,8] (by decide))
            (kuTailCells entered pointer 20 16 (by decide) eb)
        · obtain ⟨v, post, r, fr⟩ := evaluate_hash_aligned32 entered pointer _ _ p h w nl
            (kuWordCells entered pointer 32 fits al eb [0,8,16,24] (by decide))
          exact ⟨v, post, r, fr⟩
        · exact evaluate_hash_aligned52 entered pointer _ _ p h w nl
            (kuWordCells entered pointer 52 fits al eb [0,8,16,24,32,40] (by decide))
            (kuTailCells entered pointer 52 48 (by decide) eb)
      obtain ⟨v, post, r, fr⟩ := run
      refine ⟨v, post, ?_, fr⟩
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cond]
      simp only [show ¬(1 : BitVec 64) = 0 by decide, r]
      rfl
    · have cond := eval_hash_unaligned_cond entered pointer p al
      obtain ⟨v, post, r, fr⟩ := evaluate_hash_unaligned entered pointer _ _ n p h w nl sup eb
      refine ⟨v, post, ?_, fr⟩
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,cond]
      simp only [if_pos, r]
  obtain ⟨value, post, sel, ticks, memory, globals, code, addresses, endian⟩ := selected
  rw [source_hash_scoped_body,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have seedShape : shapeEqHOL .one (shapeOfHOLExact (.val (.word (14695981039346656037 : BitVec 64)))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos seedShape,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have wordShape : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos wordShape,sel]
  exact ⟨value,_,rfl,ticks,memory,globals,code,addresses,endian⟩

end ev
#print axioms evaluate_source_hashK
end InitECandidate.Runtime
