import InitECandidate.Runtime.ValidateHeadersPrefixReach
import InitECandidate.Runtime.AllocationDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def validateHeadersHsSize (n : BitVec 64) : BitVec 64 := n * (8#64) + (8#64)
def validateHeadersHashesSize (n : BitVec 64) : BitVec 64 := n * (32#64) + (32#64)
def validateHeadersHsArgument : ExpHOL 64 :=
  .op .add [.panop .mul [.var .local (ofString "n"),.const 8],.const 8]
def validateHeadersHashesArgument : ExpHOL 64 :=
  .op .add [.panop .mul [.var .local (ofString "n"),.const 32],.const 32]

theorem source_validate_headers_hs : validateHeadersAt 1 =
    .decCall (ofString "hs") .one (ofString "alloc") [validateHeadersHsArgument] (validateHeadersAt 2) := rfl

theorem source_validate_headers_hashes : validateHeadersAt 2 =
    .decCall (ofString "hashes") .one (ofString "alloc") [validateHeadersHashesArgument] (validateHeadersAt 3) := rfl

theorem validate_headers_allocation_sizes (n : BitVec 64) (small : n.toNat ≤ 256) :
    (validateHeadersHsSize n).toNat = n.toNat * 8 + 8 ∧
    (validateHeadersHashesSize n).toNat = n.toNat * 32 + 32 := by
  have eight : (n * (8#64)).toNat = n.toNat * 8 := by
    rw [BitVec.toNat_mul]; change (n.toNat * 8) % 2^64 = n.toNat * 8
    exact Nat.mod_eq_of_lt (by omega)
  have thirtyTwo : (n * (32#64)).toNat = n.toNat * 32 := by
    rw [BitVec.toNat_mul]; change (n.toNat * 32) % 2^64 = n.toNat * 32
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · unfold validateHeadersHsSize
    rw [BitVec.toNat_add_of_lt (by rw [eight]; change n.toNat * 8 + 8 < 2^64; omega),eight]; rfl
  · unfold validateHeadersHashesSize
    rw [BitVec.toNat_add_of_lt (by rw [thirtyTwo]; change n.toNat * 32 + 32 < 2^64; omega),thirtyTwo]; rfl

/-- The two original header-buffer allocations reach the actual loop setup
or terminate through allocator failure, with exact intermediate heap records. -/
theorem validate_headers_allocations_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (n heap : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496) (budget : 4 ≤ s.clock) :
    Reaches s (validateHeadersAt 1)
      (fun post => ∃ first : PanSemStateFiniteExact 64 F,
        AllocationDeclarationReady s (ofString "hs") heap (validateHeadersHsSize n) first ∧
        AllocationDeclarationReady first (ofString "hashes") (allocationEnd heap (validateHeadersHsSize n))
          (validateHeadersHashesSize n) post)
      4 (validateHeadersAt 3) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [validateHeadersHsArgument] =
      some [.val (.word (validateHeadersHsSize n))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [validateHeadersHsArgument,validateHeadersHsSize,evalListHOLExact,evalHOLExact,atCount,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  have first := evaluate_allocation_declaration_reaches s validateHeadersHsArgument (ofString "hs") heap
    (validateHeadersHsSize n) (validateHeadersAt 2) args code atHeap capped (by omega)
  rw [← source_validate_headers_hs] at first
  have firstClock : Reaches s (validateHeadersAt 1)
      (fun next => AllocationDeclarationReady s (ofString "hs") heap (validateHeadersHsSize n) next ∧
        s.clock ≤ next.clock + 2) 2 (validateHeadersAt 2) := by
    rcases first with ⟨next,allocation,spent,remaining,agreement⟩ | aborted
    · exact Or.inl ⟨next,⟨allocation,spent⟩,spent,remaining,agreement⟩
    · exact Or.inr aborted
  apply reaches_trans s (validateHeadersAt 1) (validateHeadersAt 2) (validateHeadersAt 3) _ _ 2 2 firstClock
  intro next facts
  obtain ⟨allocation,spent⟩ := facts
  have allocationKept := allocation
  obtain ⟨locals,memory,installed,domain,globals,cap,extent,alignment⟩ := allocation
  have nKept : next.locals.lookup (ofString "n") = some (.val (.word n)) := by
    rw [locals]; simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atCount
  have nextHeap : next.globals.lookup (ofString "heap_ptr") =
      some (.val (.word (allocationEnd heap (validateHeadersHsSize n)))) := by
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have nextArgs : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a)) [validateHeadersHashesArgument] =
      some [.val (.word (validateHeadersHashesSize n))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [validateHeadersHashesArgument,validateHeadersHashesSize,evalListHOLExact,evalHOLExact,nKept,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  have second := evaluate_allocation_declaration_reaches next validateHeadersHashesArgument (ofString "hashes")
    (allocationEnd heap (validateHeadersHsSize n)) (validateHeadersHashesSize n) (validateHeadersAt 3)
    nextArgs (installed.trans code) nextHeap cap (by omega)
  rw [← source_validate_headers_hashes] at second
  exact reaches_mono next (validateHeadersAt 2) (validateHeadersAt 3) _ _ 2 2 (le_refl _)
    (fun post ready => ⟨next,allocationKept,ready⟩) second

/-- The actual guard and both allocations reach loop setup in four ticks
or terminate earlier, carrying execution-derived header-count and buffer facts. -/
theorem validate_headers_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (n heap : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496) (budget : 4 ≤ s.clock) :
    Reaches s (validateHeadersAt 0)
      (fun post => n.toNat ≤ 256 ∧ ∃ first : PanSemStateFiniteExact 64 F,
        AllocationDeclarationReady s (ofString "hs") heap (validateHeadersHsSize n) first ∧
        AllocationDeclarationReady first (ofString "hashes") (allocationEnd heap (validateHeadersHsSize n))
          (validateHeadersHashesSize n) post)
      4 (validateHeadersAt 3) := by
  apply reaches_trans s (validateHeadersAt 0) (validateHeadersAt 1) (validateHeadersAt 3) _ _ 0 4
    (validate_headers_count_prefix_reaches s n code atCount)
  intro next facts
  obtain ⟨same,small⟩ := facts
  subst next
  exact reaches_mono s (validateHeadersAt 1) (validateHeadersAt 3) _ _ 4 4 (le_refl _)
    (fun post ready => ⟨small,ready⟩) (validate_headers_allocations_reaches s n heap code atCount atHeap capped budget)

#print axioms validate_headers_allocation_sizes
#print axioms validate_headers_allocations_reaches
#print axioms validate_headers_prefix_reaches
end InitECandidate.Runtime
