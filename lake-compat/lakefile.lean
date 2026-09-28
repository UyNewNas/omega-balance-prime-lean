import Lake

open System Lake DSL

package «omega-balance-lean-proofs-compat»

/-!
`plby/lean-proofs@8822f7d...` assumes in its `post_update` hook that its
transitive packages are visible below `pkg.dir/.lake/packages`.

Lake 4.34 materializes inherited Git dependencies in the root workspace package
directory. This compatibility package is required before `lean-proofs-latest`.
Its post-update hook exposes that root package directory at the nested path the
pinned upstream hook expects. The upstream hook itself still runs afterwards
and performs its original patch checks and applications.

No proof source or theorem statement is modified.
-/

post_update _ do
  let root ← getRootPackage
  let rootPackages := root.dir / ".lake" / "packages"
  let leanProofs := rootPackages / "lean-proofs-latest" / "src" / "latest"
  if !(← leanProofs.pathExists) then
    return
  let leanProofsLake := leanProofs / ".lake"
  IO.FS.createDirAll leanProofsLake
  let nestedPackages := leanProofsLake / "packages"
  if ← nestedPackages.pathExists then
    return
  let source ← IO.FS.realPath rootPackages
  let result ← IO.Process.output {
    cmd := "ln"
    args := #["-s", source.toString, nestedPackages.toString]
  }
  if result.exitCode != 0 then
    error s!"failed to expose root Lake packages to lean-proofs:\n{result.stderr}"
