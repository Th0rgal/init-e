import InitECandidate.Runtime.HashFindIterationReturnedOccupied
import InitECandidate.Runtime.WhileReturnedActiveInvariant
import InitECandidate.Runtime.MemKeepProgram
import InitECandidate.Runtime.HashTableValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Any return from the actual probe loop selects an occupied in-range slot.
This uses successful execution, without an aligned/readable query premise. -/
theorem hash_find_loop_returned_occupied {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (initial capacity used : BitVec 64) (bits : Nat) (value : ValueHOL 64)
    (power : capacity.toNat = 2 ^ bits)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word initial)))
    (inside : initial.toNat < capacity.toNat)
    (atCapacity : s.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (atUsed : s.locals.lookup (ofString "used") = some (.val (.word used)))
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s hashFindLoop = (some (.returned value),post)) :
    ∃ index : BitVec 64, value = .val (.word index) ∧ index.toNat < capacity.toNat ∧
      hashOccupancyRead s used index ≠ some 0 := by
  let Inv : ∀ {G : Type}, PanSemStateFiniteExact 64 G → Prop := fun {_} state =>
    ∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index)) ∧
      index.toNat < capacity.toNat ∧
      state.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
      state.locals.lookup (ofString "used") = some (.val (.word used)) ∧
      state.code = originalRuntimeCode ∧ hashOccupancyRead state used = hashOccupancyRead s used
  have supported : keepsM goodMem hashFindIteration = true := by decide_cbv
  have invariant := while_returned_active_invariant (hashProbeOccupied (ofString "i")) hashFindIteration Inv
    (fun v => ∃ index : BitVec 64, v = .val (.word index) ∧ index.toNat < capacity.toNat ∧
      hashOccupancyRead s used index ≠ some 0)
    (by
      intro G state facts
      obtain ⟨index,idx,lt,cap,usedLocal,installed,reads⟩ := facts
      exact ⟨index,idx,lt,cap,usedLocal,installed,reads⟩)
    (by
      intro G state v out facts active returned
      obtain ⟨index,idx,lt,cap,usedLocal,installed,reads⟩ := facts
      obtain ⟨word,evaluated,nonzero⟩ := active
      obtain ⟨same,occupied⟩ := hash_find_iteration_returned_occupied state out index used word v idx usedLocal
        evaluated nonzero returned
      exact ⟨index,same,lt,by rw [← reads]; exact occupied⟩)
    (by
      intro G state out facts flowing
      obtain ⟨index,idx,lt,cap,usedLocal,installed,reads⟩ := facts
      rcases flowing with normal | continued
      · have next := hashFindIteration_probe state out index capacity idx cap normal
        have capKeep := evaluate_avoidsLocal_flowing (ofString "cap") hashFindIteration (by decide) state
          (by rw [normal]; exact Or.inl rfl)
        have usedKeep := evaluate_avoidsLocal_flowing (ofString "used") hashFindIteration (by decide) state
          (by rw [normal]; exact Or.inl rfl)
        have memory := evaluate_keeps_mem hashFindIteration supported state installed
        have metadata := evaluateHOLFiniteState_metadata state hashFindIteration
        rw [normal] at capKeep usedKeep memory metadata
        refine ⟨hashProbeNext index capacity,next,?_,capKeep.trans cap,usedKeep.trans usedLocal,
          metadata.1.trans installed,?_⟩
        · rw [hashProbeNext_toNat index capacity bits power lt]
          exact Nat.mod_lt _ (by rw [power]; exact Nat.two_pow_pos bits)
        · exact (hashOccupancyRead_after_read state out used memory metadata.2.1 metadata.2.2.1).trans reads
      · exact absurd (congrArg Prod.fst continued) (evaluate_noTopContinue hashFindIteration (by decide) state))
  exact invariant s.clock s rfl ⟨initial,atIndex,inside,atCapacity,atUsed,code,rfl⟩ value post
    (by unfold hashFindLoop at run; exact run)

#print axioms hash_find_loop_returned_occupied
end InitECandidate.Runtime
