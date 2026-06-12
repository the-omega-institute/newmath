import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.RootConsumerCoverage
import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.RootTransportAccountability

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootTransportDownstreamCoverage [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route rootRead transportRead consumerRead
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution →
      Cont shift substitution ledger →
        Cont substitution depth audit →
          Cont ledger audit route →
            Cont route ledger rootRead →
              Cont rootRead audit transportRead →
                Cont route audit rootRead →
                  Cont rootRead route consumerRead →
                    Cont consumerRead transportRead downstream →
                      PkgSig bundle downstream pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row value ∨ hsame row depth ∨
                                hsame row ledger ∨ hsame row audit ∨ hsame row route ∨
                                  hsame row rootRead ∨ hsame row transportRead ∨
                                    hsame row consumerRead ∨ hsame row downstream)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont ledger audit route ∧
                                Cont rootRead audit transportRead ∧
                                  Cont rootRead route consumerRead ∧
                                    Cont consumerRead transportRead downstream ∧
                                      PkgSig bundle downstream pkg)
                            hsame ∧
                          UnaryHistory downstream := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeLedgerRoot rootAuditTransport routeAuditRoot rootRouteConsumer
    consumerTransportDownstream downstreamPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary ledgerUnary routeLedgerRoot
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed rootUnary auditUnary rootAuditTransport
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed rootUnary routeUnary rootRouteConsumer
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed consumerUnary transportUnary consumerTransportDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row depth ∨ hsame row ledger ∨
              hsame row audit ∨ hsame row route ∨ hsame row rootRead ∨
                hsame row transportRead ∨ hsame row consumerRead ∨ hsame row downstream)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ledger audit route ∧ Cont rootRead audit transportRead ∧
              Cont rootRead route consumerRead ∧ Cont consumerRead transportRead downstream ∧
                PkgSig bundle downstream pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro downstream ⟨hsame_refl downstream, downstreamUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceData.left))))))))
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, ledgerAuditRoute, rootAuditTransport, rootRouteConsumer,
          consumerTransportDownstream, downstreamPkg⟩
  }
  exact ⟨cert, downstreamUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
