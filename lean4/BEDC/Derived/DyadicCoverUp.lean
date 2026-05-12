import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicCoverPacket [AskSetup] [PackageSetup]
    (centers radii intervals mesh window transport routes provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
    UnaryHistory mesh ∧ UnaryHistory window ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        UnaryHistory endpoint ∧ Cont centers radii intervals ∧ Cont intervals mesh window ∧
          Cont window routes endpoint ∧ hsame nameCert endpoint ∧ PkgSig bundle endpoint pkg

theorem DyadicCoverPacket_namecert_obligations [AskSetup] [PackageSetup]
    {centers radii intervals mesh window transport routes provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCoverPacket centers radii intervals mesh window transport routes provenance nameCert
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              DyadicCoverPacket centers radii intervals mesh window transport routes provenance
                nameCert endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory centers ∧ UnaryHistory radii ∧ UnaryHistory intervals ∧
          UnaryHistory mesh ∧ UnaryHistory window ∧ Cont centers radii intervals ∧
            Cont intervals mesh window ∧ Cont window routes endpoint ∧
              PkgSig bundle endpoint pkg := by
  intro packet
  have centerUnary : UnaryHistory centers :=
    packet.left
  have radiiUnary : UnaryHistory radii :=
    packet.right.left
  have intervalsUnary : UnaryHistory intervals :=
    packet.right.right.left
  have meshUnary : UnaryHistory mesh :=
    packet.right.right.right.left
  have windowUnary : UnaryHistory window :=
    packet.right.right.right.right.left
  have centersRadiiIntervals : Cont centers radii intervals :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have intervalsMeshWindow : Cont intervals mesh window :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have windowRoutesEndpoint : Cont window routes endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            DyadicCoverPacket centers radii intervals mesh window transport routes provenance
              nameCert endpoint bundle pkg)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro endpoint (And.intro (hsame_refl endpoint) packet)
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    · intro row source
      exact source.left
    · intro row source
      exact And.intro source.left endpointPkg
  exact
    ⟨cert, centerUnary, radiiUnary, intervalsUnary, meshUnary, windowUnary,
      centersRadiiIntervals, intervalsMeshWindow, windowRoutesEndpoint, endpointPkg⟩

end BEDC.Derived.DyadicCoverUp
