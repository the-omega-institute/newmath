import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FanTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FanTheoremPacket [AskSetup] [PackageSetup]
    (tree bar depth window transport traversal provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tree ∧ UnaryHistory bar ∧ UnaryHistory depth ∧ UnaryHistory window ∧
    UnaryHistory transport ∧ UnaryHistory traversal ∧ UnaryHistory provenance ∧
      UnaryHistory nameCert ∧ UnaryHistory endpoint ∧ Cont tree bar depth ∧
        Cont depth window endpoint ∧ Cont transport traversal provenance ∧
          PkgSig bundle endpoint pkg

theorem FanTheoremPacket_namecert_obligations [AskSetup] [PackageSetup]
    {tree bar depth window transport traversal provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              FanTheoremPacket tree bar depth window transport traversal provenance nameCert
                endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory tree ∧ UnaryHistory bar ∧ UnaryHistory depth ∧ UnaryHistory window ∧
          Cont tree bar depth ∧ Cont depth window endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨treeUnary, barUnary, depthUnary, windowUnary, _transportUnary, _traversalUnary,
    _provenanceUnary, _nameCertUnary, _endpointUnary, treeBarDepth, depthWindowEndpoint,
    _transportTraversalProvenance, endpointPkg⟩ := packet
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧
          FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
            bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, packetWitness⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            FanTheoremPacket tree bar depth window transport traversal provenance nameCert endpoint
              bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              FanTheoremPacket tree bar depth window transport traversal provenance nameCert
                endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
    }
  exact
    ⟨cert, treeUnary, barUnary, depthUnary, windowUnary, treeBarDepth, depthWindowEndpoint,
      endpointPkg⟩

end BEDC.Derived.FanTheoremUp
