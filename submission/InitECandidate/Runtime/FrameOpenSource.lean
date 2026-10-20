import InitECandidate.Runtime.FrameNewWholeReturnedFunding
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def frameOpenAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_frame_open)

theorem source_frame_open_0 : frameOpenAt 0=.dec (ofString "parent") .one (.var .global (ofString "ev")) (frameOpenAt 1):=rfl
theorem source_frame_open_1 : frameOpenAt 1=.decCall (ofString "child") .one (ofString "frame_new") [.var .local (ofString "msg")] (frameOpenAt 2):=rfl
theorem source_frame_open_2 : frameOpenAt 2=.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 104] (frameOpenAt 3):=rfl
theorem source_frame_open_3 : frameOpenAt 3=.seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "rec"),.const 104]) (frameOpenAt 4):=rfl
theorem source_frame_open_4 : frameOpenAt 4=
 .seq (.store (frameNewLocalAddress (ofString "rec") 0) (.var .local (ofString "parent")))
 (.seq (.store (frameNewLocalAddress (ofString "rec") 8) (.var .global (ofString "cur_cont")))
 (.seq (.store (frameNewLocalAddress (ofString "rec") 16) (.var .local (ofString "kind")))
 (.seq (.store (frameNewLocalAddress (ofString "rec") 40) (.var .local (ofString "msg"))) (frameOpenAt 8)))):=rfl
theorem source_frame_open_8 : frameOpenAt 8=.seq (.assign .global (ofString "ev") (.var .local (ofString "child")))
 (.seq (.assign .global (ofString "cur_cont") (.var .local (ofString "rec"))) (.return (.var .local (ofString "child")))):=rfl
#print axioms source_frame_open_0
#print axioms source_frame_open_1
#print axioms source_frame_open_2
#print axioms source_frame_open_3
#print axioms source_frame_open_4
#print axioms source_frame_open_8
end InitECandidate.Runtime
