import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionCarrier_decision_refusal_surface [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert decisionRead endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont diagonal halt decisionRead →
        Cont decisionRead route endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HaltingDistinctionCarrier question trace diagonal halt classifier route
                      provenance cert bundle pkg ∧
                    hsame row diagonal)
                (fun row : BHist => hsame row diagonal ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont diagonal halt decisionRead ∧ Cont decisionRead route endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                      hsame row diagonal)
                hsame ∧
              UnaryHistory decisionRead ∧ UnaryHistory endpoint ∧
                Cont diagonal halt decisionRead ∧ Cont decisionRead route endpoint ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier diagonalHaltDecision decisionRouteEndpoint endpointPkg
  have carrierFull :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨_questionUnary, _traceUnary, diagonalUnary, haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have decisionUnary : UnaryHistory decisionRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltDecision
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed decisionUnary routeUnary decisionRouteEndpoint
  have sourceAtDiagonal :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
            bundle pkg ∧
        hsame diagonal diagonal :=
    And.intro carrierFull (hsame_refl diagonal)
  have semanticCert :
      SemanticNameCert
          (fun row : BHist =>
            HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
                cert bundle pkg ∧
              hsame row diagonal)
          (fun row : BHist => hsame row diagonal ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont diagonal halt decisionRead ∧ Cont decisionRead route endpoint ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                hsame row diagonal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro diagonal sourceAtDiagonal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact source.left
        · exact hsame_trans (hsame_symm sameRows) source.right
    }
    pattern_sound := by
      intro row source
      exact And.intro source.right (unary_transport_symm diagonalUnary source.right)
    ledger_sound := by
      intro row source
      exact
        ⟨diagonalHaltDecision, decisionRouteEndpoint, provenancePkg, endpointPkg,
          source.right⟩
  }
  exact
    ⟨semanticCert, decisionUnary, endpointUnary, diagonalHaltDecision,
      decisionRouteEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionUp
