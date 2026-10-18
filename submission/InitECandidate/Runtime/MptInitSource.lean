import InitECandidate.Runtime.GlobalAllocationPrefix
import InitECandidate.Runtime.KeccakInitializerCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def mptInitAllocations : List (MlS × BitVec 64) :=
  [(ofString "empty_trie_root",32),(ofString "empty_code_hash",32),(ofString "mpt_nib_scratch",64),
   (ofString "mpt_hash_scratch",40),(ofString "mpt_key_scratch",16)]
def mptInitFirstArguments : List (ExpHOL 64) :=
  [.var .global (ofString "mpt_hash_scratch"),.const 1,.var .global (ofString "empty_trie_root")]
def mptInitSecondArguments : List (ExpHOL 64) :=
  [.var .global (ofString "mpt_hash_scratch"),.const 0,.var .global (ofString "empty_code_hash")]
def mptInitHashTail : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "keccak256") mptInitFirstArguments)
    (.seq (.call (some (none,none)) (ofString "keccak256") mptInitSecondArguments) (.return (.const 0)))
def mptInitFinish : ProgHOL 64 :=
  .seq (.storeByte (.var .global (ofString "mpt_hash_scratch")) (.const 128)) mptInitHashTail

theorem source_mptInit_body : sourceFunctionBody Guest.guestFn_mpt_init =
    globalAllocationProgram mptInitAllocations mptInitFinish := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem mptInit_finish_globals_frame : OriginalGlobalsFrame mptInitFinish := by
  apply originalGlobalsFrame_sequence
  · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
  · apply originalGlobalsFrame_sequence
    · exact keccak_call_globals_frame _
    · apply originalGlobalsFrame_sequence
      · exact keccak_call_globals_frame _
      · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

#print axioms source_mptInit_body
#print axioms mptInit_finish_globals_frame
end InitECandidate.Runtime
