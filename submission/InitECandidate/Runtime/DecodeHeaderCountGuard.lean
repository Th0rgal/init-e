import InitECandidate.Runtime.OriginalDecodeHeaderCode
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.StatelessInputSource
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def decodeHeaderAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_decode_header)
def decodeHeaderCountGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "n")) (.const 23))
    (.assign .local (ofString "is_current") (.const 1))
    (.ite (.cmp .notEqual (.var .local (ofString "n")) (.const 21))
      (.raise (ofString "HdrErr") (.const 11)) .skip)

theorem source_decode_header_body : sourceFunctionBody Guest.guestFn_decode_header = decodeHeaderAt 0 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_decode_header_count : decodeHeaderAt 6 = .seq decodeHeaderCountGuard (decodeHeaderAt 7) := rfl

theorem source_decode_header_current : decodeHeaderAt 5 =
    .dec (ofString "is_current") .one (.const 0) (decodeHeaderAt 6) := rfl

theorem source_decode_header_allocation : decodeHeaderAt 7 =
    .decCall (ofString "h") .one (ofString "alloc") [.const 248] (decodeHeaderAt 8) := rfl

/-- The actual header-count guard accepts exactly 21 legacy or 23 current fields,
with the matching flag. It is clock-free and rejects every other count. -/
theorem decode_header_count_guard_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (n : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word (0#64)))) :
    Reaches s (decodeHeaderAt 6)
      (fun post => (n = 21 ∧ post = s) ∨
        (n = 23 ∧ post = setVarHOLFinite (ofString "is_current") (.val (.word (1#64))) s))
      0 (decodeHeaderAt 7) := by
  classical
  rw [source_decode_header_count]
  apply runBounded_seq_reaches s decodeHeaderCountGuard (decodeHeaderAt 7) _ 0
    (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega))
  · intro v
    exact evaluate_noDirectReturn decodeHeaderCountGuard rfl s v
  · intro post normal
    by_cases current : n = 23
    · have guard : evaluateHOLFiniteState s decodeHeaderCountGuard =
          (none,setVarHOLFinite (ofString "is_current") (.val (.word (1#64))) s) := by
        simp [decodeHeaderCountGuard,evaluateHOLFiniteState_ite,evalHOLExact,atCount,current,
          Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_assign,lookupKvarHOLFinite,
          isValidValueHOLFinite,shapeOfHOLExact,shapeEqHOL,atFlag,setKvarHOLFinite,setVarHOLFinite]
      rw [guard] at normal
      exact Or.inr ⟨current,(Prod.mk.inj normal).2.symm⟩
    · by_cases legacy : n = 21
      · have guard : evaluateHOLFiniteState s decodeHeaderCountGuard = (none,s) := by
          simp [decodeHeaderCountGuard,evaluateHOLFiniteState_ite,evalHOLExact,atCount,legacy,
            Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
        rw [guard] at normal
        exact Or.inl ⟨legacy,(Prod.mk.inj normal).2.symm⟩
      · have currentWord : n ≠ (23#64) := current
        have legacyWord : n ≠ (21#64) := legacy
        have guard : evaluateHOLFiniteState s decodeHeaderCountGuard =
            evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 11)) := by
          simp [decodeHeaderCountGuard,evaluateHOLFiniteState_ite,evalHOLExact,atCount,currentWord,legacyWord,
            Compiler.Encoders.Asm.wordCmpHOL]
        have noNormal : (evaluateHOLFiniteState s (.raise (ofString "HdrErr") (.const 11))).1 ≠ none := by
          rw [evaluateHOLFiniteState_raise]
          split
          · dsimp only; split <;> simp
          · simp
        rw [guard] at normal
        exact False.elim (noNormal (congrArg Prod.fst normal))

#print axioms source_decode_header_count
#print axioms source_decode_header_allocation
#print axioms decode_header_count_guard_reaches
end InitECandidate.Runtime
