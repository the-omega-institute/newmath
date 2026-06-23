import BEDC.Derived.MetaCICParallelDiamondFrontierUp

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicParallelDiamondFrontierRoute [AskSetup] [PackageSetup]
    {premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicParallelDiamondFrontierCarrier premise peak join residual checker fragment
        bounded obstruction transport replay provenance localName bundle pkg ->
      Cont premise peak routeRead ->
        PkgSig bundle localName pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row premise ∨ hsame row peak ∨ hsame row join ∨
                  hsame row residual ∨ hsame row checker ∨ hsame row fragment ∨
                    hsame row bounded ∨ hsame row obstruction ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                        hsame row routeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont premise peak routeRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: MetacicParallelDiamondFrontierCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier route localNamePkg
  obtain ⟨premiseUnary, peakUnary, _joinUnary, _residualUnary, _checkerUnary,
    _fragmentUnary, _boundedUnary, _obstructionUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed premiseUnary peakUnary route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row premise ∨ hsame row peak ∨ hsame row join ∨ hsame row residual ∨
              hsame row checker ∨ hsame row fragment ∨ hsame row bounded ∨
                hsame row obstruction ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont premise peak routeRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, route, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, routeUnary⟩

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
