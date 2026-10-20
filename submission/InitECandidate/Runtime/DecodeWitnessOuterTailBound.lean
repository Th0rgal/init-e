import InitECandidate.Runtime.DecodeWitnessInputPrefix
import InitECandidate.Runtime.MemConstCallBound
import InitECandidate.Runtime.NodeNewLeafUniformBound
import InitECandidate.Runtime.WitnessTraversalWrapperUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Exact successful-node hash attachment suffix, including failing allocations/accesses. -/
def decodeWitnessAttachHash : ProgHOL 64 :=
 .ite (.cmp .notEqual (.var .local (ofString "nd")) (.const 0))
  (.decCall (ofString "h") .one (ofString "alloc") [.const 32]
   (.seq (.call (some (none,none)) (ofString "memcpy")
     [.var .local (ofString "h"),.var .local (ofString "root_hash"),.const 32])
    (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.var .local (ofString "h"))))) .skip

theorem source_decode_witness_attach_hash : decodeWitnessAt 5 =
 .seq decodeWitnessAttachHash (.return (.var .local (ofString "nd"))) := by
 unfold decodeWitnessAt decodeWitnessAttachHash sourceFunctionBody
 rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl

theorem decode_witness_attach_hash_bounded : ProgBounded (decodeWitnessAt 5) 18 := by
 rw [source_decode_witness_attach_hash]
 have copy : ProgBounded (.call (some (none,none)) (ofString "memcpy")
     [.var .local (ofString "h"),.var .local (ofString "root_hash"),.const 32]) 16 := by
   exact memcpy_const_progBounded _ _ 32 (by decide)
 have store : ProgBounded (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.var .local (ofString "h"))) 0 := ProgBounded.straight _ rfl
 have tail : ProgBounded (.seq (.call (some (none,none)) (ofString "memcpy")
     [.var .local (ofString "h"),.var .local (ofString "root_hash"),.const 32])
    (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.var .local (ofString "h")))) 16 := by
  intro F state code budget
  exact ProgBounded.seq copy store state code budget
 have allocator : FunBounded (ofString "alloc") 1 := ⟨_,_,_,originalRuntimeCode_allocation_lookup,by
  intro F state code budget
  have bounded := evaluate_source_alloc_uniform_bounded state code budget
  exact ⟨bounded.1,bounded.2.1,bounded.2.2.1⟩⟩
 have allocation : ProgBounded (.decCall (ofString "h") .one (ofString "alloc") [.const 32]
  (.seq (.call (some (none,none)) (ofString "memcpy")
     [.var .local (ofString "h"),.var .local (ofString "root_hash"),.const 32])
    (.store (.op .add [.var .local (ofString "nd"),.const 24]) (.var .local (ofString "h"))))) 18 := by
  intro F state code budget
  exact ProgBounded.decCall allocator (ofString "h") .one [.const 32] tail state code budget
 have attach : ProgBounded decodeWitnessAttachHash 18 := by
  exact ProgBounded.ite _ allocation (ProgBounded.weaken (ProgBounded.straight .skip rfl) (by omega))
 intro F state code budget
 exact ProgBounded.seq attach (ProgBounded.straight _ rfl) state code budget
#print axioms source_decode_witness_attach_hash
#print axioms decode_witness_attach_hash_bounded
end InitECandidate.Runtime
