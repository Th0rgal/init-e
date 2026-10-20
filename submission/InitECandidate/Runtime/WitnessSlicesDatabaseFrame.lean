import InitECandidate.Runtime.RunAttemptSelectedParentInitializedDatabases
import InitECandidate.Runtime.NodedbEmptySliceRetarget
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- Actual old-memory frame exported by the two original database builds
preserves the concrete input-prefix array for every nonempty witness list. -/
theorem witness_slices_after_database_frame {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (si first second array count input length heap statePad pad output : BitVec 64)
 (ceiling : Nat) (linked : WitnessArrayLinked s si first second array count input length heap)
 (above : count.toNat=0 ∨ ceiling≤array.toNat)
 (stateBelow : statePad.toNat+200≤ceiling) (padBelow : pad.toNat+136≤ceiling)
 (outputBelow : output.toNat+32≤ceiling) (domain : post.memaddrs=s.memaddrs)
 (frame : ∀address : BitVec 64,address.toNat<heap.toNat→¬MWin statePad 200 address→¬MWin pad 136 address→
  ¬MWin output 32 address→post.memory address=s.memory address) :
 RlpSliceInputPrefix post array input length count.toNat := by
 rcases above with empty|above
 · intro index inside;omega
 · exact RlpSliceInputPrefix.after_memory_between s post array count input length heap ceiling linked.slices
    above linked.arrayEnd domain (fun address hi lo=>frame address hi (mwin_below (by omega))
     (mwin_below (by omega)) (mwin_below (by omega)))
#print axioms witness_slices_after_database_frame
end InitECandidate.Runtime
