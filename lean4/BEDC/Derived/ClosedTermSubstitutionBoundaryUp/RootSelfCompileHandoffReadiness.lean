import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootSelfCompileHandoffReadiness [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead auditReplay handoff
      operationRead selfCompileRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit operationRead ->
              Cont route audit compilerRead ->
                Cont audit route auditReplay ->
                  Cont auditReplay compilerRead handoff ->
                    Cont operationRead handoff selfCompileRead ->
                      PkgSig bundle handoff pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row selfCompileRead)
                            (fun row : BHist =>
                              Cont operationRead handoff row ∧ PkgSig bundle handoff pkg)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle handoff pkg)
                            hsame ∧
                          UnaryHistory operationRead ∧ UnaryHistory compilerRead ∧
                            UnaryHistory auditReplay ∧ UnaryHistory handoff ∧
                              UnaryHistory selfCompileRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditOperation routeAuditCompiler auditRouteReplay replayCompilerHandoff
    operationHandoffSelf handoffPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have operationUnary : UnaryHistory operationRead :=
    unary_cont_closed routeUnary auditUnary routeAuditOperation
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed routeUnary auditUnary routeAuditCompiler
  have auditReplayUnary : UnaryHistory auditReplay :=
    unary_cont_closed auditUnary routeUnary auditRouteReplay
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed auditReplayUnary compilerUnary replayCompilerHandoff
  have selfCompileUnary : UnaryHistory selfCompileRead :=
    unary_cont_closed operationUnary handoffUnary operationHandoffSelf
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro selfCompileRead (hsame_refl selfCompileRead)
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
        exact
          ⟨cont_result_hsame_transport operationHandoffSelf (hsame_symm source),
            handoffPkg⟩
      ledger_sound := by
        intro _row source
        exact ⟨unary_transport selfCompileUnary (hsame_symm source), handoffPkg⟩
    }
  · exact
      ⟨operationUnary, compilerUnary, auditReplayUnary, handoffUnary, selfCompileUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
