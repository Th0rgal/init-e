import InitECandidate.Runtime.RunAttemptEntryAllWitnessSelectedRootReach
import InitECandidate.Runtime.RunAttemptSelectedParentStateInitBound
import InitECandidate.Runtime.RunAttemptHeadersInitializedGlobals
import InitECandidate.Runtime.NodedbInputCost
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Entire original selected-root/all-witness postcondition, with its actual states
and witnesses named so later composition retains every header fact. -/
def RunAttemptSelectedWitnessFacts {F : Type} (s final validated : PanSemStateFiniteExact 64 F)
 (si payload array count inputLength heap keccakState keccakPad stateArray stateCount codeArray codeCount liveHeap parent root : BitVec 64) : Prop :=
RunAttemptHeaderValidationFacts (setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
          validated si array count (2713731432#64) inputLength (2713714688#64) (2701135872#64) heap keccakState keccakPad 2713731432 ∧
        count ≠ 0 ∧
        final = setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word count))
          (setGlobalHOLFinite (ofString "block_hashes")
            (.val (.word (allocationEnd heap (validateHeadersHsSize count))))
            (setVarHOLFinite (ofString "parent") (.val (.word parent))
              (setVarHOLFinite (ofString "nh") (.val (.word count)) validated))) ∧
        final.locals.lookup (ofString "parent") = some (.val (.word parent)) ∧
        final.globals.lookup (ofString "heap_ptr") = some (.val (.word liveHeap)) ∧
        final.memory (parent + (32#64)) = .word root ∧ final.memaddrs (parent + (32#64)) ∧
        parent.toNat + 248 ≤ liveHeap.toNat ∧
        (allocationEnd heap (validateHeadersHsSize count)).toNat + count.toNat * 32 + 32 ≤ parent.toNat ∧
        WitnessArrayLinked final si 40 48 stateArray stateCount (2713731432#64) inputLength liveHeap ∧
        WitnessArrayLinked final si 56 64 codeArray codeCount (2713731432#64) inputLength liveHeap ∧
        final.locals.lookup (ofString "si") = some (.val (.word si)) ∧
        final.code = originalRuntimeCode ∧ final.memaddrs = s.memaddrs ∧
        liveHeap.toNat % 8 = 0
/-- Entire actual two-database/selected-parent metadata plus derived initializer bound. -/
def RunAttemptInitializedWitnessFacts {F : Type} (s final : PanSemStateFiniteExact 64 F)
 (heap total₁ array₁ total₂ array₂ statePad pad output parent word : BitVec 64) : Prop :=
∃ midHeap finalHeap : BitVec 64,
        final.locals = (s.locals.update (ofString "nodedb",.val (.word heap))).update
          (ofString "codedb",.val (.word midHeap)) ∧
        final.memaddrs = s.memaddrs ∧ final.code = s.code ∧ final.be = s.be ∧
        final.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        final.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        final.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        final.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        heap.toNat ≤ midHeap.toNat ∧ midHeap.toNat ≤ finalHeap.toNat ∧
        finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
        HashTableValuesIn heap (NodedbSliceTargets array₁ total₁) final ∧
        HashTableValuesIn midHeap (NodedbSliceTargets array₂ total₂) final ∧
        NodedbTableAt final heap finalHeap total₁ ∧ NodedbTableAt final midHeap finalHeap total₂ ∧
        (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
          final.memaddrs a) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w → ¬ MWin pad 136 w →
          ¬ MWin output 32 w → final.memory w = s.memory w) ∧
        final.locals.lookup (ofString "parent") = some (.val (.word parent)) ∧
        final.memory (parent + 32#64) = .word word ∧
        final.memaddrs (parent + 32#64) ∧
        parent.toNat + 248 ≤ finalHeap.toNat ∧
        evalListHOLFinite final (h := fun a => Classical.propDecidable (final.memaddrs a))
          runAttemptStateInitArguments =
          some [.val (.word heap),.val (.word word),.val (.word midHeap)] ∧
        lookupCodeHOLFinite final.code.lookup (ofString "state_init")
          [.val (.word heap),.val (.word word),.val (.word midHeap)] =
          some (sourceFunctionBody Guest.guestFn_state_init,stateInitCallee heap word midHeap,.one) ∧
        (∀ key, key ∈ nodedbInitializerGlobals → final.globals.lookup key=s.globals.lookup key) ∧
        (stateInitSourceCeiling+1≤final.clock → RunBounded
          (callEntryStateHOLFinite final (stateInitCallee heap word midHeap))
          (sourceFunctionBody Guest.guestFn_state_init) stateInitSourceCeiling)
/-- Uniform fixed budget for entry/header validation and both actual database calls. -/
def runAttemptEntryInitializerCost : Nat := validateHeadersBodyCost 134217712+1+2*nodedbInputCallCost 134217712
#print axioms RunAttemptSelectedWitnessFacts
#print axioms RunAttemptInitializedWitnessFacts
end InitECandidate.Runtime
