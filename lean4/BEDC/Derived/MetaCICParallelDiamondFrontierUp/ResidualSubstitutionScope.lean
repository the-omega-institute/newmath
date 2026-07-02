import BEDC.Derived.MetaCICParallelDiamondFrontierUp

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicParallelDiamondFrontierResidualSubstitutionScope [AskSetup] [PackageSetup]
    {P K J R S C B O H T G N residualRead checkerRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier P K J R S C B O H T G N bundle pkg ->
      Cont P R residualRead ->
        Cont residualRead S checkerRead ->
          Cont checkerRead C handoffRead ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row P ∨ hsame row K ∨ hsame row J ∨ hsame row R ∨
                      hsame row S ∨ hsame row C ∨ hsame row B ∨ hsame row O ∨
                        hsame row H ∨ hsame row T ∨ hsame row G ∨ hsame row N ∨
                          hsame row residualRead ∨ hsame row checkerRead ∨
                            hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont P R residualRead ∧
                      Cont residualRead S checkerRead ∧
                        Cont checkerRead C handoffRead ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory residualRead ∧ UnaryHistory checkerRead ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: MetacicParallelDiamondFrontierCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier residualRoute checkerRoute handoffRoute localNamePkg
  obtain ⟨premiseUnary, _peakUnary, _joinUnary, residualUnary, checkerUnary,
    fragmentUnary, _boundedUnary, _obstructionUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed premiseUnary residualUnary residualRoute
  have checkerReadUnary : UnaryHistory checkerRead :=
    unary_cont_closed residualReadUnary checkerUnary checkerRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed checkerReadUnary fragmentUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row K ∨ hsame row J ∨ hsame row R ∨
              hsame row S ∨ hsame row C ∨ hsame row B ∨ hsame row O ∨
                hsame row H ∨ hsame row T ∨ hsame row G ∨ hsame row N ∨
                  hsame row residualRead ∨ hsame row checkerRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P R residualRead ∧
              Cont residualRead S checkerRead ∧
                Cont checkerRead C handoffRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffReadUnary⟩
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
      exact ⟨source.right, residualRoute, checkerRoute, handoffRoute, localNamePkg⟩
  }
  exact ⟨cert, residualReadUnary, checkerReadUnary, handoffReadUnary⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
