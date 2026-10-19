import InitECandidate.Runtime.DecodeHeaderRlpEntryReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeHeaderKindGuard : ProgHOL 64 :=
  .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "top"))) (.const 1))
    (.raise (ofString "HdrErr") (.const 10)) .skip

theorem source_decode_header_kind_guard : decodeHeaderAt 1 = .seq decodeHeaderKindGuard (decodeHeaderAt 2) := rfl

theorem source_decode_header_slices : decodeHeaderAt 2 =
    .decCall (ofString "lst") (.comb [.one,.one]) (ofString "rlp_list_to_slices")
      [.rfield 1 (.var .local (ofString "top")),.rfield 2 (.var .local (ofString "top"))] (decodeHeaderAt 3) := rfl

theorem source_decode_header_array : decodeHeaderAt 3 =
    .dec (ofString "arr") .one (.rfield 0 (.var .local (ofString "lst"))) (decodeHeaderAt 4) := rfl

theorem source_decode_header_count_local : decodeHeaderAt 4 =
    .dec (ofString "n") .one (.rfield 1 (.var .local (ofString "lst"))) (decodeHeaderAt 5) := rfl

/-- The real kind check reaches list parsing unchanged only for kind 1. -/
theorem decode_header_kind_guard_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (kind pointer size consumed : BitVec 64) (code : s.code = originalRuntimeCode)
    (atTop : s.locals.lookup (ofString "top") =
      some (.rStruct [.val (.word kind),.val (.word pointer),.val (.word size),.val (.word consumed)])) :
    Reaches s (decodeHeaderAt 1) (fun post => post = s ∧ kind = 1) 0 (decodeHeaderAt 2) := by
  classical
  rw [source_decode_header_kind_guard]
  apply runBounded_seq_reaches s decodeHeaderKindGuard (decodeHeaderAt 2) _ 0
    (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega))
  · intro v
    exact evaluate_noDirectReturn decodeHeaderKindGuard rfl s v
  · intro post normal
    by_cases accepted : kind = 1
    · have guard : evaluateHOLFiniteState s decodeHeaderKindGuard = (none,s) := by
        simp [decodeHeaderKindGuard,evaluateHOLFiniteState_ite,evalHOLExact,atTop,accepted,
          Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
      rw [guard] at normal
      exact ⟨(Prod.mk.inj normal).2.symm,accepted⟩
    · have rejected : kind ≠ (1#64) := accepted
      have guard : evaluateHOLFiniteState s decodeHeaderKindGuard =
          evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 10)) := by
        simp [decodeHeaderKindGuard,evaluateHOLFiniteState_ite,evalHOLExact,atTop,rejected,
          Compiler.Encoders.Asm.wordCmpHOL]
      have noNormal : (evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 10))).1 ≠ none := by
        rw [evaluateHOLFiniteState_raise]
        split
        · dsimp only; split <;> simp
        · simp
      rw [guard] at normal
      exact False.elim (noNormal (congrArg Prod.fst normal))

/-- The actual initial full parse and kind guard reach list-to-slices with
a bounded list payload and the decoder's old workspace/memory restored. -/
theorem decode_header_list_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeHeaderRlpCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 0)
      (fun ready => ∃ input size : BitVec 64,
        size.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
        pointer.toNat ≤ input.toNat ∧ input.toNat + size.toNat ≤ pointer.toNat + length.toNat ∧
        input.toNat + size.toNat < 2^64 ∧
        ready.locals = s.locals.update (ofString "top",
          .rStruct [.val (.word (1#64)),.val (.word input),.val (.word size),.val (.word length)]) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ name : MlS, ready.globals.lookup name = s.globals.lookup name) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → ready.memory address = s.memory address))
      (decodeHeaderRlpCost inputLimit) (decodeHeaderAt 2) := by
  apply reaches_trans s (decodeHeaderAt 0) (decodeHeaderAt 1) (decodeHeaderAt 2) _ _ (decodeHeaderRlpCost inputLimit) 0
    (decode_header_rlp_entry_reaches s pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound
      limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget)
  intro parsed facts
  obtain ⟨kind,input,size,_,sizeBound,positive,starts,ends,fits,locals,domain,installed,globals,memory⟩ := facts
  have atTop : parsed.locals.lookup (ofString "top") =
      some (.rStruct [.val (.word kind),.val (.word input),.val (.word size),.val (.word length)]) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  apply reaches_mono parsed (decodeHeaderAt 1) (decodeHeaderAt 2) _ _ 0 0 (le_refl _) ?_
    (decode_header_kind_guard_reaches parsed kind input size length (installed.trans code) atTop)
  intro post kept
  obtain ⟨same,accepted⟩ := kept
  subst post
  subst kind
  exact ⟨input,size,sizeBound,positive,starts,ends,fits,locals,domain,installed,globals,memory⟩

#print axioms decode_header_kind_guard_reaches
#print axioms decode_header_list_entry_reaches
end InitECandidate.Runtime
