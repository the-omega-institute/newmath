import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionClassifierStability [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert classifierRead
      transported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont question cert classifierRead →
        Cont classifierRead route transported →
          PkgSig bundle transported pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row cert ∧
                    HaltingDistinctionCarrier question trace diagonal halt classifier route
                      provenance cert bundle pkg)
                (fun row : BHist =>
                  hsame row cert ∧ UnaryHistory row ∧ Cont question cert classifierRead)
                (fun _row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle transported pkg ∧
                    Cont classifierRead route transported)
                hsame ∧
              UnaryHistory classifierRead ∧ UnaryHistory transported := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier questionCertRead classifierRouteTransported transportedPkg
  have carrierWitness :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨questionUnary, _traceUnary, _diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed questionUnary certUnary questionCertRead
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed classifierReadUnary routeUnary classifierRouteTransported
  have sourceAtCert :
      hsame cert cert ∧
        HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
          bundle pkg :=
    And.intro (hsame_refl cert) carrierWitness
  have certObject :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cert ∧
              HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
                cert bundle pkg)
          (fun row : BHist =>
            hsame row cert ∧ UnaryHistory row ∧ Cont question cert classifierRead)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle transported pkg ∧
              Cont classifierRead route transported)
          hsame := {
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
        intro _row _other sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro row source
      exact
        ⟨source.left, unary_transport certUnary (hsame_symm source.left),
          questionCertRead⟩
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, transportedPkg, classifierRouteTransported⟩
  }
  exact ⟨certObject, classifierReadUnary, transportedUnary⟩

end BEDC.Derived.HaltingDistinctionUp
