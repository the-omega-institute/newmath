import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row cert ∧ UnaryHistory row)
        (fun row : BHist =>
          KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
            provenance cert bundle pkg ∧ hsame row cert)
        (fun _row : BHist =>
          Cont source graph edgeAdmission ∧ Cont edgeAdmission classifierLift target ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier
  have carrierPacket := carrier
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _edgeUnary, _liftUnary, _transportUnary,
    _routesUnary, _provenanceUnary, certUnary, sourceGraphEdge, edgeLiftTarget,
    _transportRoutesProvenance, provenancePkg, certPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro cert ⟨hsame_refl cert, certUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨carrierPacket, source.left⟩
    ledger_sound := by
      intro _row _source
      exact ⟨sourceGraphEdge, edgeLiftTarget, provenancePkg, certPkg⟩
  }

end BEDC.Derived.KernelMorphismUp
