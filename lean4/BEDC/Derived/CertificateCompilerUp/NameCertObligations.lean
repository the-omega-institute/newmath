import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert landingRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      Cont graph landing landingRead →
        Cont landingRead routes publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row publicRead ∧
                  CertificateCompilerCarrier source target graph landing routes transport
                    provenance cert bundle pkg)
              (fun row : BHist =>
                Cont source graph landing ∧ Cont graph landing landingRead ∧
                  Cont landingRead routes publicRead ∧ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ hsame cert (append provenance target) ∧
                  PkgSig bundle cert pkg ∧ PkgSig bundle publicRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont PkgSig
  intro carrier graphLandingRead landingReadRoutesPublic publicPkg
  have carrierPacket := carrier
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, certPkg⟩ := carrier
  have landingReadUnary : UnaryHistory landingRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed landingReadUnary routesUnary landingReadRoutesPublic
  exact {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, carrierPacket⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro row sourceRow
      exact ⟨sourceGraphLanding, graphLandingRead, landingReadRoutesPublic, sourceRow.left⟩
    ledger_sound := by
      intro row sourceRow
      exact
        ⟨unary_transport_symm publicReadUnary sourceRow.left, certMatchesEndpoint, certPkg,
          publicPkg⟩
  }

end BEDC.Derived.CertificateCompilerUp
