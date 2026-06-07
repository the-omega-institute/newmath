import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootRouteExhaustion [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            PkgSig bundle route pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row route)
                  (fun row : BHist => Cont ledger audit row ∧ PkgSig bundle route pkg)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle route pkg)
                  hsame ∧
                UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute routePkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row route)
          (fun row : BHist => Cont ledger audit row ∧ PkgSig bundle route pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle route pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro route (hsame_refl route)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact ⟨cont_result_hsame_transport ledgerAuditRoute (hsame_symm source), routePkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport routeUnary (hsame_symm source), routePkg⟩
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary⟩

theorem ClosedTermSubstitutionBoundaryRootDownstreamReadiness [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit downstream ->
              PkgSig bundle downstream pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row downstream)
                    (fun _row : BHist =>
                      Cont ledger audit route ∧ Cont route audit downstream ∧
                        PkgSig bundle downstream pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle downstream pkg)
                    hsame ∧
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory downstream := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditDownstream downstreamPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed routeUnary auditUnary routeAuditDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream)
          (fun _row : BHist =>
            Cont ledger audit route ∧ Cont route audit downstream ∧
              PkgSig bundle downstream pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle downstream pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstream (hsame_refl downstream)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row _source
      exact ⟨ledgerAuditRoute, routeAuditDownstream, downstreamPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport downstreamUnary (hsame_symm source), downstreamPkg⟩
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, downstreamUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
