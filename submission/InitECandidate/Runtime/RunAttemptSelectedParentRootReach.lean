import InitECandidate.Runtime.RunAttemptBlockHashesReach
import InitECandidate.Runtime.ValidateHeadersRoomedAt4Returned
/-!
The caller selects the header that `validate_headers` actually returned.

`run_attempt` declares `parent := vh[nh-1]` - the final header pointer of the buffer the header
function returned - and reads the state root at `parent + 32`.  This module takes the selected
facts the header function's own returned contract establishes (cell, root word, domain, live heap)
plus the initialized buffer, and derives the actual declaration at `runAttemptAt 5`, exporting the
typed local `parent` together with the same root word, domain and live heap binding.  No caller
scope `h` and no parent selector callback is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual `parent := vh[nh-1]` declaration reaches `runAttemptAt 6` with the typed local
`parent` equal to the header the header function selected, and the selected state root word, its
domain and the live heap binding still readable in the ready state. -/
theorem run_attempt_selected_parent_root_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs hashes count header word heap : BitVec 64)
    (atVh : s.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word hs),.val (.word hashes)]))
    (atNh : s.locals.lookup (ofString "nh") = some (.val (.word count)))
    (initialized : HeaderPointerPrefix s hs count.toNat) (countNonzero : count ≠ 0)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cell : s.memory (hs + (count - 1) * 8) = .word header)
    (rootWord : s.memory (header + 32#64) = .word word)
    (rootDomain : s.memaddrs (header + 32#64)) :
    Reaches s (runAttemptAt 5)
      (fun ready => ∃ parent : BitVec 64,
        ready = setVarHOLFinite (ofString "parent") (.val (.word parent)) s ∧
        parent = header ∧
        ready.memory (header + 32#64) = .word word ∧
        ready.memaddrs (header + 32#64) ∧
        ready.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
      0 (runAttemptAt 6) := by
  obtain ⟨domain,parent,parentCell⟩ := initialized.last s hs count countNonzero
  have parentEq : parent = header :=
    HolWordLab.word.inj (parentCell.symm.trans cell)
  have reached := run_attempt_parent_reaches (F := F) s hs hashes count parent atVh atNh domain parentCell
  refine reaches_mono s (runAttemptAt 5) (runAttemptAt 6) _ _ _ _ (le_refl 0) ?_ reached
  intro ready readyEq
  refine ⟨parent, readyEq, parentEq, ?_, ?_, ?_⟩
  · rw [readyEq]
    simpa [setVarHOLFinite] using rootWord
  · rw [readyEq]
    exact rootDomain
  · rw [readyEq]
    simpa [setVarHOLFinite] using heapGlobal


/-- **The selected parent and its state root survive the block-hash global assignments.**  From
`runAttemptAt 5`, the actual declaration binds `parent`, and after the two global assignments the
typed `parent` local, the selected state root word, its domain, the live heap binding and the two
block-hash globals are all readable at `runAttemptAt 9`, with no clock spent. -/
theorem run_attempt_selected_parent_root_at9_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs hashes count header word heap : BitVec 64)
    (atVh : s.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word hs),.val (.word hashes)]))
    (atNh : s.locals.lookup (ofString "nh") = some (.val (.word count)))
    (initialized : HeaderPointerPrefix s hs count.toNat) (countNonzero : count ≠ 0)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (cell : s.memory (hs + (count - 1) * 8) = .word header)
    (rootWord : s.memory (header + 32#64) = .word word)
    (rootDomain : s.memaddrs (header + 32#64)) :
    Reaches s (runAttemptAt 5)
      (fun final => ∃ parent : BitVec 64,
        final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes") (.val (.word hashes))
            (setVarHOLFinite (ofString "parent") (.val (.word parent)) s)) ∧
        final.locals.lookup (ofString "parent") = some (.val (.word parent)) ∧ parent = header ∧
        final.memory (header + 32#64) = .word word ∧
        final.memaddrs (header + 32#64) ∧
        final.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
        final.globals.lookup (ofString "block_hashes") = some (.val (.word hashes)) ∧
        final.globals.lookup (ofString "block_hashes_n") = some (.val (.word count)))
      0 (runAttemptAt 9) := by
  have first := run_attempt_selected_parent_root_reaches (F := F) s hs hashes count header word heap
    atVh atNh initialized countNonzero heapGlobal cell rootWord rootDomain
  refine reaches_trans s (runAttemptAt 5) (runAttemptAt 6) (runAttemptAt 9) _ _ 0 0 first ?_
  intro middle middleReady
  obtain ⟨parent,middleEq,parentEq,rootWordMid,domainMid,heapMid⟩ := middleReady
  subst middleEq
  have hVh : (ofString "vh") ≠ ofString "parent" := by decide
  have hNh : (ofString "nh") ≠ ofString "parent" := by decide
  have atVhMid : (setVarHOLFinite (ofString "parent") (.val (.word parent)) s).locals.lookup
      (ofString "vh") = some (.rStruct [.val (.word hs),.val (.word hashes)]) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm hVh,atVh]
  have atNhMid : (setVarHOLFinite (ofString "parent") (.val (.word parent)) s).locals.lookup
      (ofString "nh") = some (.val (.word count)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm hNh,atNh]
  have assigned := run_attempt_block_hashes_reaches (F := F)
    (setVarHOLFinite (ofString "parent") (.val (.word parent)) s) hs hashes count atVhMid atNhMid
  refine reaches_mono _ (runAttemptAt 6) (runAttemptAt 9) _ _ _ _ (le_refl 0) ?_ assigned
  intro final finalEq
  have hHeap : (ofString "heap_ptr") ≠ ofString "block_hashes" := by decide
  have hHeapN : (ofString "heap_ptr") ≠ ofString "block_hashes_n" := by decide
  refine ⟨parent,finalEq,?_,parentEq,?_,?_,?_,?_,?_⟩
  · rw [finalEq]
    simp [setGlobalHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm (by decide : (ofString "parent") ≠ ofString "block_hashes"),
      Ne.symm (by decide : (ofString "parent") ≠ ofString "block_hashes_n")]
  · rw [finalEq]
    simpa [setGlobalHOLFinite,setVarHOLFinite] using rootWord
  · rw [finalEq]
    simpa [setGlobalHOLFinite,setVarHOLFinite] using domainMid
  · rw [finalEq]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm hHeap,Ne.symm hHeapN]
      using heapMid
  · rw [finalEq]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    intro blocked
    exact absurd blocked (by decide)
  · rw [finalEq]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms run_attempt_selected_parent_root_at9_reaches
#print axioms run_attempt_selected_parent_root_reaches
end InitECandidate.Runtime
