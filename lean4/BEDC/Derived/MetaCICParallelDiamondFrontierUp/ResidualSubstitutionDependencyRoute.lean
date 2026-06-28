import BEDC.Derived.MetaCICParallelDiamondFrontierUp

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicParallelDiamondFrontierResidualSubstitutionDependencyRoute [AskSetup]
    [PackageSetup]
    {premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName criticalRead candidateRead residualRead dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier premise peak join residual checker fragment
        bounded obstruction transport replay provenance localName bundle pkg →
      Cont premise peak criticalRead →
        Cont criticalRead join candidateRead →
          Cont candidateRead residual residualRead →
            Cont residualRead obstruction dependencyRead →
              PkgSig bundle dependencyRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row premise ∨ hsame row peak ∨ hsame row join ∨
                        hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                          hsame row bounded ∨ hsame row obstruction ∨
                            hsame row transport ∨ hsame row replay ∨
                              hsame row provenance ∨ hsame row localName ∨
                                hsame row criticalRead ∨ hsame row candidateRead ∨
                                  hsame row residualRead ∨ hsame row dependencyRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont premise peak criticalRead ∧
                        Cont criticalRead join candidateRead ∧
                          Cont candidateRead residual residualRead ∧
                            Cont residualRead obstruction dependencyRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle dependencyRead pkg)
                    hsame ∧ UnaryHistory criticalRead ∧ UnaryHistory candidateRead ∧
                  UnaryHistory residualRead ∧ UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: MetacicParallelDiamondFrontierCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier criticalRoute candidateRoute residualRoute dependencyRoute dependencyPkg
  obtain ⟨premiseUnary, peakUnary, joinUnary, residualUnary, _checkerUnary,
    _fragmentUnary, _boundedUnary, obstructionUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, provenancePkg⟩ := carrier
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed premiseUnary peakUnary criticalRoute
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed criticalUnary joinUnary candidateRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary residualUnary residualRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed residualReadUnary obstructionUnary dependencyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨
              hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                    hsame row criticalRead ∨ hsame row candidateRead ∨
                      hsame row residualRead ∨ hsame row dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont premise peak criticalRead ∧
              Cont criticalRead join candidateRead ∧
                Cont candidateRead residual residualRead ∧
                  Cont residualRead obstruction dependencyRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle dependencyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dependencyRead ⟨hsame_refl dependencyRead, dependencyUnary⟩
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
      repeat right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, criticalRoute, candidateRoute, residualRoute, dependencyRoute,
          provenancePkg, dependencyPkg⟩
  }
  exact ⟨cert, criticalUnary, candidateUnary, residualReadUnary, dependencyUnary⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
