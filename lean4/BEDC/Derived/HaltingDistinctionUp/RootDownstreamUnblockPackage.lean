import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootDownstreamUnblockPackage [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert obstructionRead
      downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont cert diagonal obstructionRead ->
        Cont obstructionRead route downstreamRead ->
          PkgSig bundle downstreamRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row downstreamRead)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont obstructionRead route downstreamRead)
                hsame ∧
              UnaryHistory downstreamRead ∧ Cont question trace diagonal ∧
                Cont diagonal halt classifier ∧ Cont classifier route cert ∧
                  Cont cert diagonal obstructionRead ∧
                    Cont obstructionRead route downstreamRead ∧
                      PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont hsame
  intro carrier certDiagonalObstruction obstructionRouteDownstream downstreamPkg
  obtain ⟨_questionUnary, _traceUnary, diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, certUnary, questionTraceDiagonal,
    diagonalHaltClassifier, classifierRouteCert, _provenancePkg⟩ := carrier
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed certUnary diagonalUnary certDiagonalObstruction
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed obstructionUnary routeUnary obstructionRouteDownstream
  have sourceAtDownstream : hsame downstreamRead downstreamRead ∧ UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have certPackage :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row downstreamRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont obstructionRead route downstreamRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstreamRead sourceAtDownstream
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, obstructionRouteDownstream⟩
  }
  exact
    ⟨certPackage, downstreamUnary, questionTraceDiagonal, diagonalHaltClassifier,
      classifierRouteCert, certDiagonalObstruction, obstructionRouteDownstream, downstreamPkg⟩

end BEDC.Derived.HaltingDistinctionUp
