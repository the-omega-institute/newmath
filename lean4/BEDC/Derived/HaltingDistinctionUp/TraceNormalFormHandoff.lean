import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionTraceNormalFormHandoff [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead normalRead endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont traceRead classifier normalRead →
          Cont normalRead diagonal endpoint →
            PkgSig bundle endpoint pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row cert ∧
                      HaltingDistinctionCarrier question trace diagonal halt classifier route
                        provenance cert bundle pkg)
                  (fun row : BHist =>
                    hsame row cert ∧ UnaryHistory traceRead ∧ UnaryHistory normalRead ∧
                      UnaryHistory endpoint)
                  (fun _row : BHist =>
                    Cont trace route traceRead ∧ Cont traceRead classifier normalRead ∧
                      Cont normalRead diagonal endpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg)
                  hsame ∧
                UnaryHistory traceRead ∧ UnaryHistory normalRead ∧
                  UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier traceRouteRead traceClassifierNormal normalDiagonalEndpoint endpointPkg
  have carrierPacket :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, _haltUnary, classifierUnary, routeUnary,
    _provenanceUnary, _certUnary, _questionTraceDiagonal, _diagonalHaltClassifier,
    _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed traceReadUnary classifierUnary traceClassifierNormal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed normalReadUnary diagonalUnary normalDiagonalEndpoint
  have sourceAtCert :
      hsame cert cert ∧
        HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
          bundle pkg :=
    And.intro (hsame_refl cert) carrierPacket
  have certObject :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cert ∧
              HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
                cert bundle pkg)
          (fun row : BHist =>
            hsame row cert ∧ UnaryHistory traceRead ∧ UnaryHistory normalRead ∧
              UnaryHistory endpoint)
          (fun _row : BHist =>
            Cont trace route traceRead ∧ Cont traceRead classifier normalRead ∧
              Cont normalRead diagonal endpoint ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro cert sourceAtCert
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
          intro _row _other sameRows sourceRow
          exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            sourceRow.right
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, traceReadUnary, normalReadUnary, endpointUnary⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨traceRouteRead, traceClassifierNormal, normalDiagonalEndpoint, provenancePkg,
            endpointPkg⟩
    }
  exact ⟨certObject, traceReadUnary, normalReadUnary, endpointUnary⟩

end BEDC.Derived.HaltingDistinctionUp
