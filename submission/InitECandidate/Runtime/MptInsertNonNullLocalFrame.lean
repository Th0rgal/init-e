import InitECandidate.Runtime.MptInsertNonNullWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertStableNames : List MlS :=
 [ofString "node",ofString "slot",ofString "level",ofString "result",ofString "key",ofString "klen",ofString "vptr",ofString "vlen"]
/-- The actual non-null dispatch writes prepared working locals, while its
source calls and lexical declarations preserve the caller traversal inputs. -/
theorem mpt_insert_nonnull_local_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (run : evaluateHOLFiniteState s mptInsertNonNullStep=(none,post)) :
 ∀name∈mptInsertStableNames,post.locals.lookup name=s.locals.lookup name := by
 intro name member
 have avoids : avoidsLocal name mptInsertNonNullStep=true := by
  simp only [mptInsertStableNames,List.mem_cons,List.not_mem_nil,or_false] at member
  simp only [mptInsertNonNullStep,mptInsertLoopStep,sourceFunctionBody,Proofs.FrontendCodecComputation.declToHOL_eq]
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
 have kept:=evaluate_avoidsLocal_flowing name mptInsertNonNullStep avoids s
 rw [run] at kept
 exact kept (Or.inl rfl)
#print axioms mpt_insert_nonnull_local_frame
end InitECandidate.Runtime
