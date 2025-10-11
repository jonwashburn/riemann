import Lean
open System

abbrev ActiveFiles : List String := [
  "no-zeros/rh/Proof/Main.lean",
  "no-zeros/rh/Proof/Export.lean",
  "no-zeros/rh/Proof/DOI.lean",
  "no-zeros/rh/Proof/AxiomsCheckLite.lean",
  "no-zeros/rh/academic_framework/Certificate.lean",
  "no-zeros/rh/academic_framework/CompletedXi.lean",
  "no-zeros/rh/academic_framework/CompletedXiSymmetry.lean",
  "no-zeros/rh/academic_framework/HalfPlaneOuterV2.lean",
  "no-zeros/rh/academic_framework/CayleyAdapters.lean",
  "no-zeros/rh/academic_framework/PoissonCayley.lean",
  "no-zeros/rh/RS/RouteB_Final.lean",
  "no-zeros/rh/RS/PinchWrappers.lean",
  "no-zeros/rh/RS/PinchIngredients.lean",
  "no-zeros/rh/RS/PinnedRemovable.lean",
  "no-zeros/rh/RS/OffZerosBridge.lean",
  "no-zeros/rh/RS/XiExtBridge.lean",
  "no-zeros/rh/RS/CRGreenOuter.lean",
  "no-zeros/rh/RS/Det2Outer.lean",
  "no-zeros/rh/RS/Det2.lean",
  "no-zeros/rh/RS/Context.lean",
  "no-zeros/rh/RS/PinchCertificate.lean",
  "no-zeros/rh/RS/SchurGlobalization.lean",
  "no-zeros/rh/RS/CertificateConstruction.lean",
  "no-zeros/rh/RS/BoundaryWedgeProof.lean",
  "no-zeros/rh/Cert/KxiWhitney.lean",
  "no-zeros/rh/Cert/KxiPPlus.lean",
  "no-zeros/rh/Cert/FactorsWitness.lean"
]

def main : IO Unit := do
  let outPath := FilePath.mk "no-zeros/ActiveProofTrack.txt"
  let mut contents := ""
  for file in ActiveFiles do
    let data ← IO.FS.readFile (FilePath.mk file)
    contents := contents ++ s!"-- BEGIN {file}\n" ++ data ++ "\n-- END {file}\n\n"
  IO.FS.writeFile outPath contents
  IO.println s!"Wrote {ActiveFiles.length} files to {outPath}"
