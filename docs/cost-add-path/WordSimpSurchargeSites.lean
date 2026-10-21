import InitECandidate.Proofs.FrontendStages.Word.FunctionsFacts
import Flapjack.Compiler.Backend.WordSimp
open Flapjack Flapjack.Compiler.Backend.WordSimp

/-- number of assigns `dropConsts cs ns` inserts -/
def dropN (cs : Spt (BitVec 64)) (ns : List Nat) : Nat := (ns.filter (fun n => (sptLookup n cs).isSome)).length

/-- constFpLoop with a count of dropConsts inserts (same recursion) -/
def cfC : WordLangProgHOL (BitVec 64) → Spt (BitVec 64) → WordLangProgHOL (BitVec 64) × Spt (BitVec 64) × Nat
  | .mustTerminate p, cs => let (p', cs', k) := cfC p cs; (.mustTerminate p', cs', k)
  | .seq p1 p2, cs =>
      let (p1', cs', k1) := cfC p1 cs
      let (p2', cs'', k2) := cfC p2 cs'
      (.seq p1' p2', cs'', k1 + k2)
  | .ite cmp lhs rhs p1 p2, cs =>
      match sptLookup lhs cs, getVarImmCs rhs cs with
      | some clhs, some crhs =>
          if Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs then cfC p1 cs else cfC p2 cs
      | _, _ =>
          let (p1', p1cs, k1) := cfC p1 cs
          let (p2', p2cs, k2) := cfC p2 cs
          (.ite cmp lhs rhs p1' p2', sptInterEq p1cs p2cs, k1 + k2)
  | p@(.call ret _ args handler), cs =>
      let r := constFpLoop p cs
      match ret, handler with
      | some (n, names, retHandler, _, _), none =>
          let cs' := deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names)))
          let (_, _, k) := cfC retHandler cs'
          (r.1, r.2, dropN cs args + k)
      | _, _ => (r.1, r.2, dropN cs args)
  | p@(.ffi _ x1 x2 x3 x4 _), cs => let r := constFpLoop p cs; (r.1, r.2, dropN cs [x1, x2, x3, x4])
  | p@(.alloc n _), cs => let r := constFpLoop p cs; (r.1, r.2, dropN cs [n])
  | p@(.install r1 r2 r3 r4 _), cs => let r := constFpLoop p cs; (r.1, r.2, dropN cs [r1, r2, r3, r4])
  | .loop names body exitNames, _ => let (b, _, k) := cfC body .ln; (.loop names b exitNames, .ln, k)
  | p, cs => let r := constFpLoop p cs; (r.1, r.2, 0)

/-- number of successful if-hoists in simpDuplicateIf -/
def hoistN : WordLangProgHOL (BitVec 64) → Nat
  | .mustTerminate q => hoistN q
  | .call ret _ _ handler =>
      (match ret with | some (_, _, q, _, _) => hoistN q | none => 0) +
      (match handler with | some (_, q, _, _) => hoistN q | none => 0)
  | .ite _ _ _ a b => hoistN a + hoistN b
  | .seq p1 p2 =>
      hoistN p1 + hoistN p2 + (match tryIfHoist1 (simpDuplicateIf p1) (simpDuplicateIf p2) with | none => 0 | some _ => 1)
  | .loop _ b _ => hoistN b
  | _ => 0

/-- ops folded to non-binary by constFp: count `.op` with arity < 2 after constFp -/
partial def badOps : WordLangExpHOL (BitVec 64) → Nat
  | .op .sub as => (if as.length == 2 then 0 else 1) + (as.map badOps).sum
  | .op _ as => (if as.length ≥ 2 then 0 else 1) + (as.map badOps).sum
  | .load a => badOps a
  | .shift _ a b => badOps a + badOps b
  | _ => 0

/-- trailing statements of a left-nested seq spine, last first -/
def trail : WordLangProgHOL (BitVec 64) → List (WordLangProgHOL (BitVec 64))
  | .seq a b => trail b ++ trail a
  | .skip => []
  | p => [p]

/-- max multiplicity of const re-assignment of one arg register right before a call -/
partial def multK : WordLangProgHOL (BitVec 64) → Nat
  | .seq a b =>
      let here := match b with
        | .call _ _ args _ =>
            let pre := (trail a).takeWhile (fun q => match q with | .assign n (.const _) => args.contains n | _ => false)
            let regs := pre.filterMap (fun q => match q with | .assign n _ => some n | _ => none)
            (regs.map (fun r => regs.count r)).foldl max 0
        | _ => 0
      max here (max (multK a) (multK b))
  | .mustTerminate q => multK q
  | .call ret _ _ handler =>
      max (match ret with | some (_, _, q, _, _) => multK q | none => 0)
          (match handler with | some (_, q, _, _) => multK q | none => 0)
  | .ite _ _ _ a b => max (multK a) (multK b)
  | .loop _ b _ => multK b
  | _ => 0

def flat : WordLangProgHOL (BitVec 64) → List (WordLangProgHOL (BitVec 64))
  | .seq a b => flat a ++ flat b
  | .skip => []
  | p => [p]

partial def sites (pre : String) (p : WordLangProgHOL (BitVec 64)) : List String :=
  let items := flat p
  (List.range items.length).foldl (fun acc i =>
    let q := items.getD i .skip
    let before := (items.take i).reverse
    let here := match q with
      | .call ret dest args _ =>
          let k := (before.takeWhile (fun x => match x with | .assign n (.const _) => args.contains n | _ => false)).length
          let lab := match ret with | some (_, _, _, l1, l2) => s!"{l1}.{l2}" | none => "tail"
          [s!"{pre} call {dest} ret={lab} args={args.length} trailingConst={k}"]
      | .alloc n _ =>
          let k := (before.takeWhile (fun x => match x with | .assign m (.const _) => m == n | _ => false)).length
          [s!"{pre} alloc trailingConst={k}"]
      | _ => []
    let inner := match q with
      | .mustTerminate b => sites pre b
      | .call ret _ _ handler =>
          (match ret with | some (_, _, k, _, _) => sites (pre ++ "K") k | none => []) ++
          (match handler with | some (_, h, _, _) => sites (pre ++ "H") h | none => [])
      | .ite _ _ _ a b => sites (pre ++ "T") a ++ sites (pre ++ "E") b
      | .loop _ b _ => sites (pre ++ "L") b
      | _ => []
    acc ++ here ++ inner) []

def parseK (l : String) : String × Nat :=
  let parts := l.splitOn " trailingConst="
  (parts.headD "", (parts.getD 1 "0").toNat!)

#eval do
  let mut tot := 0; let mut retS := 0; let mut tailS := 0; let mut allocS := 0; let mut dupl := 0; let mut maxS := 0
  for (lab, _, p) in InitECandidate.Proofs.FrontendStages.Word.outputs do
    let src : List (String × Nat) := (sites "" (seqAssoc .skip p)).map parseK
    let out : List (String × Nat) := (sites "" (compileExp p)).map parseK
    -- key without path prefix
    let key : String → String := fun x => ((x.splitOn " call ").getD 1 ((x.splitOn " alloc").getD 1 x))
    let srcMap : List (String × Nat) := src.map (fun (x, k) => (key x, k))
    for (x, k) in out do
      let k0 : Nat := ((srcMap.find? (fun (yk : String × Nat) => yk.1 == key x)).map Prod.snd).getD 0
      if k > k0 then
        let d := k - k0
        tot := tot + d; maxS := max maxS d
        if (x.splitOn "ret=tail").length > 1 then tailS := tailS + 1; IO.println s!"TAIL {lab} {x} +{d}"
        else if (x.splitOn "alloc").length > 1 then allocS := allocS + 1; IO.println s!"ALLOC {lab} {x} +{d}"
        else retS := retS + 1
    let outKeys : List String := out.map (fun (xk : String × Nat) => key xk.1)
    let retKeys : List String := outKeys.filter (fun (x : String) => (x.splitOn "ret=tail").length == 1 && (x.splitOn "alloc").length == 1)
    if retKeys.length != retKeys.eraseDups.length then dupl := dupl + 1
  IO.println s!"surchargeAssigns(executed-site sum)={tot} retSites={retS} tailSites={tailS} allocSites={allocS} maxPerSite={maxS} fnsWithDuplicatedReturnLabels={dupl}"
