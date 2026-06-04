import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootDepthValueBridgeDeterminacy [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route rootRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit rootRead ->
              Cont source depth bridgeRead ->
                PkgSig bundle rootRead pkg ->
                  hsame rootRead rootRead ∧ UnaryHistory source ∧ UnaryHistory value ∧
                    UnaryHistory depth ∧ UnaryHistory ledger ∧ UnaryHistory audit ∧
                      UnaryHistory route ∧ UnaryHistory rootRead ∧ UnaryHistory bridgeRead ∧
                        Cont source value shift ∧ Cont shift depth substitution ∧
                          Cont source depth bridgeRead ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditRoot sourceDepthBridge rootPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sourceUnary depthUnary sourceDepthBridge
  exact
    ⟨hsame_refl rootRead, sourceUnary, valueUnary, depthUnary, ledgerUnary, auditUnary,
      routeUnary, rootUnary, bridgeUnary, sourceValueShift, shiftDepthSubstitution,
      sourceDepthBridge, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
