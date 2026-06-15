import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionObstructionSiblingJointPackage [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead inscriptionRead
      obstructionRead packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont trace route traceRead ->
        Cont diagonal route inscriptionRead ->
          Cont traceRead inscriptionRead obstructionRead ->
            Cont obstructionRead cert packageRead ->
              PkgSig bundle packageRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row packageRead ∧ Cont traceRead inscriptionRead obstructionRead)
                    (fun row : BHist =>
                      hsame row packageRead ∧ PkgSig bundle packageRead pkg)
                    hsame ∧
                  UnaryHistory traceRead ∧ UnaryHistory inscriptionRead ∧
                    UnaryHistory obstructionRead ∧ UnaryHistory packageRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory ProbeBundle Pkg
  intro carrier traceRoute inscriptionRoute obstructionRoute packageRoute packagePkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, _provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRoute
  have inscriptionReadUnary : UnaryHistory inscriptionRead :=
    unary_cont_closed diagonalUnary routeUnary inscriptionRoute
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed traceReadUnary inscriptionReadUnary obstructionRoute
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed obstructionReadUnary certUnary packageRoute
  have certPkg :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row packageRead ∧ Cont traceRead inscriptionRead obstructionRead)
          (fun row : BHist => hsame row packageRead ∧ PkgSig bundle packageRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro packageRead ⟨hsame_refl packageRead, packageReadUnary⟩
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
      exact ⟨source.left, obstructionRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packagePkg⟩
  }
  exact ⟨certPkg, traceReadUnary, inscriptionReadUnary, obstructionReadUnary, packageReadUnary⟩

end BEDC.Derived.HaltingDistinctionUp
