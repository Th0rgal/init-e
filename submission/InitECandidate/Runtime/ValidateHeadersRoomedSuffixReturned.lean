import InitECandidate.Runtime.ValidateHeadersParentSurvivesSecondPhase
import InitECandidate.Runtime.ValidateHeadersStoredRootsFinalParent
/-!
The actual value `validate_headers` returns, together with the selected parent.

`validate_headers` returns `rStruct[hs, hashes]`, not the selected header: the second phase returns
exactly that pair, and being a memory frame it leaves the first loop's parent cell and state root
word readable.  The selected header is loaded later by `run_attempt`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- **The suffix's actual returned contract.**  The roomed first phase at entry, its actual
returned run, and the actual second phase from the exit state give: the value returned is the
`rStruct` pair of the header-pointer buffer and hash buffer, and the final state still carries the
parent cell `hs[count-1]` with its readable state root word, its domain, the extent below the live
heap and the fixed floor below the header. -/
theorem validate_headers_roomed_suffix_returned {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s stop post : PanSemStateFiniteExact 64 F) (rank : Nat) (code : s.code = originalRuntimeCode)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (valid : ValidateHeadersStoredRootsRoomedInvariant e s rank)
    (countNonzero : e.count ≠ 0)
    (budget : validateHeadersFirstLoopCost e.inputLimit ≤ s.clock) (value : ValueHOL 64)
    (returned : (evaluateHOLFiniteState s (validateHeadersAt 4)).1 = some (.returned value))
    (atHs : stop.locals.lookup (ofString "hs") = some (.val (.word e.hs)))
    (atHashes : stop.locals.lookup (ofString "hashes") = some (.val (.word e.hashes)))
    (roomed : ValidateHeadersStoredRootsRoomedInvariant e stop 0)
    (stopCode : stop.code = originalRuntimeCode)
    (phase : evaluateHOLFiniteState stop (validateHeadersSecondAt 5) = (some (.returned value),post)) :
    value = .rStruct [.val (.word e.hs),.val (.word e.hashes)] ∧
      (∃ heap header word : BitVec 64,
        post.memory (e.hs + (e.count - 1) * 8) = .word header ∧
        post.memory (header + 32#64) = .word word ∧ post.memaddrs (header + 32#64) ∧
        header.toNat + 248 ≤ heap.toNat ∧
        e.hashes.toNat + e.count.toNat * 32 + 32 ≤ header.toNat) := by
  have shape := evaluate_validate_headers_second_phase_returned (F := F) stop e.hs e.hashes value
    post stopCode atHs atHashes phase
  obtain ⟨pair,frameMemory,_,frameDomain,_,_⟩ := shape
  obtain ⟨heap,header,word,heapGlobal,cell,rooted,domain,extent,above⟩ :=
    validate_headers_stored_roots_parent_exhausted (F := F) e stop roomed.1 countNonzero
  refine ⟨pair,heap,header,word,?_,?_,?_,?_,?_⟩
  · rw [frameMemory]
    exact cell
  · rw [frameMemory]
    exact rooted
  · exact frameDomain ▸ domain
  · exact extent
  · exact above
