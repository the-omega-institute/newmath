import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryNormalizationFrontierHandoff [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route frontierRead frontierPublic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit frontierRead ->
              Cont frontierRead depth frontierPublic ->
                PkgSig bundle frontierPublic pkg ->
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory frontierRead ∧ UnaryHistory frontierPublic ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit route ∧ Cont route audit frontierRead ∧
                          Cont frontierRead depth frontierPublic ∧
                            PkgSig bundle frontierPublic pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditFrontier frontierDepthPublic frontierPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed routeUnary auditUnary routeAuditFrontier
  have frontierPublicUnary : UnaryHistory frontierPublic :=
    unary_cont_closed frontierReadUnary depthUnary frontierDepthPublic
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, frontierReadUnary, frontierPublicUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditFrontier,
      frontierDepthPublic, frontierPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
