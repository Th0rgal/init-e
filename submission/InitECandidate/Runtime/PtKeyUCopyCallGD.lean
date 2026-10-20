import InitECandidate.Runtime.PtKeyUCopyGD
import InitECandidate.Runtime.MemcpyAlignedCall
import InitECandidate.Runtime.MemcpyAlignmentValue
/-!
The source `memcpy` when its operands are not both 8-aligned: the word loops are skipped and the byte loops copy.
The body returns `0`, the discarding call statement completes normally, memory changes only in the destination's
cells (`cpW`), and at most `n / 8 + 9` clocks are spent.  Only the aligned cells of the copied bytes need to be
addressable.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section cc
variable {F : Type}

theorem eval_memcpy_unaligned_cond (state : PanSemStateFiniteExact 64 F) (dst src : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word src)))
    (unal : (dst ||| src) &&& 7 ≠ 0) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) memcpyAlignmentCondition =
      some (.val (.word 0)) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.op .or [.var .local (ofString "dst"),.var .local (ofString "src")],.const 7]) =
        some (.val (.word ((dst ||| src) &&& 7))) := by
    simp [evalHOLExact,evalListHOLExact,dstLocal,srcLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    change (dst ||| (src ||| 0)) &&& ((7 : BitVec 64) &&& BitVec.allOnes 64) = (dst ||| src) &&& 7
    have bz : src ||| (0 : BitVec 64) = src := by exact BitVec.or_zero
    rw [bz, BitVec.and_allOnes]
  unfold memcpyAlignmentCondition
  rw [evalHOLExact, loaded]
  simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
  exact unal

/-- The byte suffix from index `i`: returns `0`, writes only `cpW`, at most `(n - i) / 8 + 7` clocks. -/
theorem cp_suffix {dst src n : BitVec 64} {M : BitVec 64 → HolWordLab 64} {D : BitVec 64 → Prop} {B : Bool}
    {G : HolFiniteMapExact MlS (ValueHOL 64)} {C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    (small : n.toNat ≤ 33806089496)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (dst + x)) ∧ D (panByteAlignHOL (src + x)))
    (s : PanSemStateFiniteExact 64 F) (hs : CpInv dst src n M D B G C s) (budget : n.toNat / 8 + 7 ≤ s.clock) :
    ∃ post, evaluateHOLFiniteState s memcpyByteSuffix = (some (.returned (.val (.word 0))), post) ∧
      s.clock ≤ post.clock + (n.toNat / 8 + 7) ∧ post.clock ≤ s.clock ∧
      post.memaddrs = D ∧ post.be = B ∧ post.globals = G ∧ post.code = C ∧ ∀ x, ¬ cpW dst n x → post.memory x = M x := by
  obtain ⟨i, li, _⟩ := hs.2.2.2.1
  have r8 : memeqByte8Rank n s ≤ n.toNat / 8 := by simp [memeqByte8Rank, li]; omega
  obtain ⟨p8, run8, cost8, rem8, inv8, z8⟩ := cp_loop8 small cells s hs (by omega)
  obtain ⟨j, lj, _⟩ := inv8.2.2.2.1
  have r1 : memeqByteRank n p8 ≤ 7 := by
    simp [memeqByte8Rank, lj] at z8
    simp [memeqByteRank, lj]; omega
  obtain ⟨p1, run1, cost1, rem1, inv1⟩ := cp_loop1 cells p8 inv8 (by omega)
  unfold memcpyByteSuffix
  rw [evaluateHOLFiniteState_seq_line780, run8]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, run1]
  dsimp only
  have ret : evaluateHOLFiniteState p1 (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite p1) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [ret]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := inv1
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · change s.clock ≤ p1.clock + (n.toNat / 8 + 7); omega
  · change p1.clock ≤ s.clock; omega
  · exact ⟨h5, h6, h7, h8, h9⟩

/-- The complete `memcpy` body with operands not both 8-aligned. -/
theorem evaluate_source_memcpy_unaligned (state : PanSemStateFiniteExact 64 F) (dst src n : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word src)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (unal : (dst ||| src) &&& 7 ≠ 0) (small : n.toNat ≤ 33806089496)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat →
      state.memaddrs (panByteAlignHOL (dst + x)) ∧ state.memaddrs (panByteAlignHOL (src + x)))
    (budget : n.toNat / 8 + 7 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memcpy) = (some (.returned (.val (.word 0))), post) ∧
      state.clock ≤ post.clock + (n.toNat / 8 + 7) ∧ post.clock ≤ state.clock ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.globals = state.globals ∧ post.code = state.code ∧
      ∀ x, ¬ cpW dst n x → post.memory x = state.memory x := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have nd : ofString "i" ≠ ofString "dst" := by decide
  have ns : ofString "i" ≠ ofString "src" := by decide
  have nn : ofString "i" ≠ ofString "n" := by decide
  have inv : CpInv dst src n state.memory state.memaddrs state.be state.globals state.code entered := by
    refine ⟨?_, ?_, ?_, ⟨0, ?_, by simp⟩, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ <;>
      simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nd, ns, nn, dstLocal, srcLocal, sizeLocal]
  have cond := eval_memcpy_unaligned_cond entered dst src
    (by simpa [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, nd] using dstLocal)
    (by simpa [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ns] using srcLocal) unal
  obtain ⟨post, run, c1, c2, hD, hB, hG, hC, hM⟩ := cp_suffix small cells entered inv budget
  have selected : evaluateHOLFiniteState entered memcpyAfterIndex = (some (.returned (.val (.word 0))), post) := by
    unfold memcpyAfterIndex
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, cond]
    simp only [if_true, evaluateHOLFiniteState_skip]
    exact run
  rw [source_memcpy_scoped_body, evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos shapeOk, selected]
  exact ⟨_, rfl, c1, c2, hD, hB, hG, hC, hM⟩

/-- The discarding `memcpy(dst, src, n)` call statement with operands not both 8-aligned. -/
theorem evaluate_memcpy_unaligned_call (state : PanSemStateFiniteExact 64 F)
    (destinationArgument sourceArgument sizeArgument : ExpHOL 64) (dst src n : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [destinationArgument,sourceArgument,sizeArgument] =
        some [.val (.word dst),.val (.word src),.val (.word n)])
    (unal : (dst ||| src) &&& 7 ≠ 0) (small : n.toNat ≤ 33806089496)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat →
      state.memaddrs (panByteAlignHOL (dst + x)) ∧ state.memaddrs (panByteAlignHOL (src + x)))
    (budget : n.toNat / 8 + 8 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy")
        [destinationArgument,sourceArgument,sizeArgument]) = (none,post) ∧
      state.clock ≤ post.clock + (n.toNat / 8 + 8) ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      ∀ x, ¬ cpW dst n x → post.memory x = state.memory x := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word dst))).update
      (ofString "src",.val (.word src))).update (ofString "n",.val (.word n))
  let entry := callEntryStateHOLFinite state callee
  have nd : ofString "n" ≠ ofString "dst" := by decide
  have ns : ofString "n" ≠ ofString "src" := by decide
  have sd : ofString "src" ≠ ofString "dst" := by decide
  have dl : entry.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,nd,sd]
  have sl : entry.locals.lookup (ofString "src") = some (.val (.word src)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,ns]
  have nl : entry.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post, body, c1, c2, hD, hB, hG, hC, hM⟩ :=
    evaluate_source_memcpy_unaligned entry dst src n dl sl nl unal small cells
      (by change n.toNat / 8 + 7 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "memcpy") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one) := by
    rw [code]; exact originalRuntimeCode_memcpy_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memcpy) dst src n (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "memcpy")
    [destinationArgument,sourceArgument,sizeArgument] [.val (.word dst),.val (.word src),.val (.word n)]
    (sourceFunctionBody Guest.guestFn_memcpy) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{post with locals := state.locals}, call, ?_, ?_, hG, hC, hD, hB, rfl, hM⟩
  · change state.clock ≤ post.clock + (n.toNat / 8 + 8)
    change state.clock - 1 ≤ post.clock + (n.toNat / 8 + 7) at c1
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at c2
    omega

end cc
#print axioms evaluate_source_memcpy_unaligned
#print axioms evaluate_memcpy_unaligned_call
end InitECandidate.Runtime
