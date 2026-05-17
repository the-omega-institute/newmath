import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootFiniteTraceClassifierExhaustion [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead pairRead endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont trace route traceRead →
        Cont question trace pairRead →
          Cont traceRead classifier endpoint →
            PkgSig bundle endpoint pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row endpoint ∧
                      HaltingDistinctionCarrier question trace diagonal halt classifier route
                        provenance cert bundle pkg)
                  (fun row : BHist =>
                    hsame row endpoint ∧ UnaryHistory traceRead ∧ UnaryHistory pairRead)
                  (fun _row : BHist =>
                    Cont trace route traceRead ∧ Cont question trace pairRead ∧
                      Cont traceRead classifier endpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg)
                  hsame ∧
                UnaryHistory traceRead ∧ UnaryHistory pairRead ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier traceRouteRead questionTracePair traceReadClassifierEndpoint endpointPkg
  have carrierFull :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨questionUnary, traceUnary, _diagonalUnary, _haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have pairReadUnary : UnaryHistory pairRead :=
    unary_cont_closed questionUnary traceUnary questionTracePair
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceReadUnary classifierUnary traceReadClassifierEndpoint
  have sourceAtEndpoint :
      hsame endpoint endpoint ∧
        HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
          bundle pkg :=
    And.intro (hsame_refl endpoint) carrierFull
  have finiteTraceCert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
                cert bundle pkg)
          (fun row : BHist =>
            hsame row endpoint ∧ UnaryHistory traceRead ∧ UnaryHistory pairRead)
          (fun _row : BHist =>
            Cont trace route traceRead ∧ Cont question trace pairRead ∧
              Cont traceRead classifier endpoint ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, traceReadUnary, pairReadUnary⟩
    ledger_sound := by
      intro _row _source
      exact
        ⟨traceRouteRead, questionTracePair, traceReadClassifierEndpoint, provenancePkg,
          endpointPkg⟩
  }
  exact ⟨finiteTraceCert, traceReadUnary, pairReadUnary, endpointUnary⟩

end BEDC.Derived.HaltingDistinctionUp
