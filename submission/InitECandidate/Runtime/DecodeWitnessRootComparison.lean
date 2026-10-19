import InitECandidate.Runtime.MemeqCall32
import InitECandidate.Runtime.StateInitJournalSource
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeWitnessAt (n : Nat) : ProgHOL 64 :=
  stateInitSpineDrop n (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt)

theorem source_decode_witness_root_comparison : decodeWitnessAt 0 =
    .decCall (ofString "is_empty") .one (ofString "memeq")
      [.var .local (ofString "root_hash"),.var .global (ofString "empty_trie_root"),.const 32]
      (decodeWitnessAt 1) := by
  unfold decodeWitnessAt sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual first witness-decoder call reaches its empty-root guard after
one clock, preserving memory, globals and domain and exposing the comparison bit. -/
theorem decode_witness_root_comparison_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (root emptyRoot : BitVec 64)
    (atRoot : s.locals.lookup (ofString "root_hash") = some (.val (.word root)))
    (atEmpty : s.globals.lookup (ofString "empty_trie_root") = some (.val (.word emptyRoot)))
    (code : s.code = originalRuntimeCode) (ticks : s.clock ≠ 0)
    (aligned : root.toNat % 8 = 0) (emptyAligned : emptyRoot.toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat),
      s.memaddrs (root + BitVec.ofNat 64 offset) ∧ s.memaddrs (emptyRoot + BitVec.ofNat 64 offset)) :
    Reaches s (decodeWitnessAt 0)
      (fun post => ∃ bit : BitVec 64, (bit = 0 ∨ bit = 1) ∧
        post.locals = s.locals.update (ofString "is_empty",.val (.word bit)) ∧
        post.clock = s.clock - 1 ∧ post.memory = s.memory ∧ post.globals = s.globals ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be)
      1 (decodeWitnessAt 1) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "root_hash"),.var .global (ofString "empty_trie_root"),.const 32] =
      some [.val (.word root),.val (.word emptyRoot),.val (.word (32#64))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atRoot,atEmpty]
  obtain ⟨bit,ready,boolean,clock,memory,locals,globals,installed,addrs,endian,run⟩ :=
    evaluate_memeq32_declaration s (.var .local (ofString "root_hash"))
      (.var .global (ofString "empty_trie_root")) (.const 32) root emptyRoot args code ticks aligned emptyAligned domain
  let post := setVarHOLFinite (ofString "is_empty") (.val (.word bit)) ready
  refine Or.inl ⟨post,⟨bit,boolean,?_,clock,memory,globals,installed,addrs,endian⟩,?_,?_,?_⟩
  · change ready.locals.update _ = _
    rw [locals]
  · change s.clock ≤ ready.clock + 1
    omega
  · change ready.clock ≤ s.clock
    omega
  · rw [source_decode_witness_root_comparison,run]
    exact scoped_restore _ _

#print axioms source_decode_witness_root_comparison
#print axioms decode_witness_root_comparison_reaches
end InitECandidate.Runtime
