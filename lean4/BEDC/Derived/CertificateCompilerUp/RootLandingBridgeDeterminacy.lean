import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_root_landing_bridge_determinacy
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead targetEndpoint
      routeEndpoint certEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame landingRead landing →
        hsame targetEndpoint target →
          hsame routeEndpoint routes →
            hsame cert certEndpoint →
              PkgSig bundle certEndpoint pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row certEndpoint ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    Cont provenance target row ∧ Cont source graph landing ∧
                      Cont landing routes target ∧ hsame landingRead landing ∧
                        hsame targetEndpoint target ∧ hsame routeEndpoint routes)
                  (fun row : BHist =>
                    PkgSig bundle row pkg ∧ hsame row (append provenance target) ∧
                      Cont source graph landing ∧ Cont landing routes target)
                  (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg SemanticNameCert
  intro carrier landingSame targetEndpointSame routeEndpointSame certEndpointSame
    certEndpointPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have certEndpointUnary : UnaryHistory certEndpoint :=
    unary_transport certUnary certEndpointSame
  have certEndpointLedger : hsame certEndpoint (append provenance target) :=
    hsame_trans (hsame_symm certEndpointSame) certMatchesEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro certEndpoint
          ⟨hsame_refl certEndpoint, certEndpointUnary, certEndpointPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      have certRow : hsame cert row :=
        hsame_trans certEndpointSame (hsame_symm sourceRow.left)
      exact
        ⟨cont_result_hsame_transport provenanceTargetCert certRow, sourceGraphLanding,
          landingRoutesTarget, landingSame, targetEndpointSame, routeEndpointSame⟩
    ledger_sound := by
      intro row sourceRow
      have rowLedger : hsame row (append provenance target) :=
        hsame_trans sourceRow.left certEndpointLedger
      exact ⟨sourceRow.right.right, rowLedger, sourceGraphLanding, landingRoutesTarget⟩
  }

end BEDC.Derived.CertificateCompilerUp
