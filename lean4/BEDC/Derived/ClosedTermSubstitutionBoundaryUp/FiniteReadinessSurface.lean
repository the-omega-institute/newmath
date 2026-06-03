import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryFiniteReadinessSurface [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer readiness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer route readiness ->
                PkgSig bundle consumer pkg ->
                  PkgSig bundle readiness pkg ->
                    UnaryHistory readiness ∧ Cont consumer route readiness ∧
                      PkgSig bundle readiness pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row readiness ∧ PkgSig bundle readiness pkg)
                          (fun row : BHist => Cont consumer route row ∧ PkgSig bundle row pkg)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle readiness pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerRouteReadiness _consumerPkg readinessPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed consumerUnary routeUnary consumerRouteReadiness
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readiness ∧ PkgSig bundle readiness pkg)
          (fun row : BHist => Cont consumer route row ∧ PkgSig bundle row pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle readiness pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro readiness ⟨hsame_refl readiness, readinessPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨consumerRouteReadiness, readinessPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport readinessUnary (hsame_symm source.left), source.right⟩
  }
  exact ⟨readinessUnary, consumerRouteReadiness, readinessPkg, cert⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
