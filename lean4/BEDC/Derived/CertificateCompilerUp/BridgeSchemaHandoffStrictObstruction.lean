import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_bridge_schema_handoff_strict_obstruction
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert obstruction bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      Cont graph landing bridgeRead →
        hsame obstruction bridgeRead →
          PkgSig bundle obstruction pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row obstruction ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun row : BHist =>
                Cont graph landing bridgeRead ∧ hsame row obstruction ∧
                  Cont source graph landing ∧ Cont landing routes target)
              (fun row : BHist =>
                PkgSig bundle row pkg ∧ hsame cert (append provenance target))
              hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier graphLandingRead obstructionRead obstructionPkg
  obtain ⟨_sourceUnary, _targetUnary, graphUnary, landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed graphUnary landingUnary graphLandingRead
  have obstructionUnary : UnaryHistory obstruction :=
    unary_transport bridgeReadUnary (hsame_symm obstructionRead)
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro obstruction
          ⟨hsame_refl obstruction, obstructionUnary, obstructionPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
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
      exact ⟨graphLandingRead, sourceRow.left, sourceGraphLanding, landingRoutesTarget⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨sourceRow.right.right, certMatchesEndpoint⟩
  }

end BEDC.Derived.CertificateCompilerUp
