import InitECandidate.Runtime.DecodeHeaderCurrentSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual legacy-header suffix performs two constant stores and the
final return without spending source clock, including any failed store/return. -/
theorem decode_header_legacy_suffix_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode)
    (flag : s.locals.lookup (ofString "is_current") = some (.val (.word (0#64)))) :
    RunBounded s (decodeHeaderAt 56) 0 := by
  have legacy : RunBounded s (.seq decodeHeaderLegacySuffix (decodeHeaderAt 57)) 0 := by
    rw [source_decode_header_return]
    exact RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega)
  have selected : evaluateHOLFiniteState s (.ite decodeHeaderCurrentCondition decodeHeaderCurrentSuffix decodeHeaderLegacySuffix) =
      evaluateHOLFiniteState s decodeHeaderLegacySuffix := by
    simp [evaluateHOLFiniteState_ite,decodeHeaderCurrentCondition,evalHOLExact,flag,Compiler.Encoders.Asm.wordCmpHOL]
  unfold RunBounded at legacy ⊢
  rw [source_decode_header_current_suffix,evaluateHOLFiniteState_seq_line780,selected]
  rw [evaluateHOLFiniteState_seq_line780] at legacy
  exact legacy

#print axioms decode_header_legacy_suffix_bounded
end InitECandidate.Runtime
