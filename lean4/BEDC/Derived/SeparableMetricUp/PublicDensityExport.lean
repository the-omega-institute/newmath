import BEDC.Derived.SeparableMetricUp.TasteGate

namespace BEDC.Derived.SeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparableMetricPublicDensityExport [AskSetup] [PackageSetup]
    {metric dense windows tolerance readback sealRow transports routes provenance localCert
      publicRead namedPublic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableMetricCarrier metric dense windows tolerance readback sealRow transports routes
        provenance localCert bundle pkg ->
      Cont readback sealRow publicRead ->
        Cont publicRead localCert namedPublic ->
          PkgSig bundle namedPublic pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row namedPublic ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row dense ∨ hsame row windows ∨
                    hsame row tolerance ∨ hsame row readback ∨ hsame row sealRow ∨
                      hsame row namedPublic)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle namedPublic pkg)
                hsame ∧
              UnaryHistory publicRead ∧ UnaryHistory namedPublic := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute namedRoute namedPkg
  obtain ⟨metricUnary, denseUnary, windowsUnary, toleranceUnary, readbackUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, localCertUnary,
      _denseWindowRoute, _toleranceReadbackRoute, _sealRoute, provenancePkg,
        _localCert⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed readbackUnary sealRowUnary publicRoute
  have namedUnary : UnaryHistory namedPublic :=
    unary_cont_closed publicUnary localCertUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedPublic ∧ UnaryHistory row) namedPublic := by
    exact ⟨hsame_refl namedPublic, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedPublic ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row dense ∨ hsame row windows ∨
              hsame row tolerance ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row namedPublic)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle namedPublic pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedPublic sourceNamed
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, publicUnary, namedUnary⟩

end BEDC.Derived.SeparableMetricUp
