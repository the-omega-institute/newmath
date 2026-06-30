import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionObservationBoundary [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert inscriptionRead
      normalFormRead obstructionRead observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont diagonal trace inscriptionRead ->
        Cont trace route normalFormRead ->
          Cont classifier route obstructionRead ->
            Cont inscriptionRead obstructionRead observationRead ->
              PkgSig bundle observationRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row observationRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row inscriptionRead ∨ hsame row normalFormRead ∨
                        hsame row obstructionRead ∨ hsame row observationRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont diagonal trace inscriptionRead ∧
                        Cont trace route normalFormRead ∧
                          Cont classifier route obstructionRead ∧
                            Cont inscriptionRead obstructionRead observationRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle observationRead pkg)
                    hsame ∧
                  UnaryHistory inscriptionRead ∧ UnaryHistory normalFormRead ∧
                    UnaryHistory obstructionRead ∧ UnaryHistory observationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier inscriptionRoute normalFormRoute obstructionRoute observationRoute
    observationPkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, _haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have inscriptionUnary : UnaryHistory inscriptionRead :=
    unary_cont_closed diagonalUnary traceUnary inscriptionRoute
  have normalFormUnary : UnaryHistory normalFormRead :=
    unary_cont_closed traceUnary routeUnary normalFormRoute
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed classifierUnary routeUnary obstructionRoute
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed inscriptionUnary obstructionUnary observationRoute
  have sourceAtObservation : hsame observationRead observationRead ∧ UnaryHistory observationRead :=
    ⟨hsame_refl observationRead, observationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row observationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row inscriptionRead ∨ hsame row normalFormRead ∨
              hsame row obstructionRead ∨ hsame row observationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont diagonal trace inscriptionRead ∧
              Cont trace route normalFormRead ∧ Cont classifier route obstructionRead ∧
                Cont inscriptionRead obstructionRead observationRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle observationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro observationRead sourceAtObservation
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, inscriptionRoute, normalFormRoute, obstructionRoute,
          observationRoute, provenancePkg, observationPkg⟩
  }
  exact ⟨cert, inscriptionUnary, normalFormUnary, obstructionUnary, observationUnary⟩

end BEDC.Derived.HaltingDistinctionUp
