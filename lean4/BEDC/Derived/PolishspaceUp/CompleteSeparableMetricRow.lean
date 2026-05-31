import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteSeparableMetricRow [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completeRead denseRead rowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceCarrier metric complete separable stream readback ledger transport replay
        provenance localName bundle pkg ->
      Cont complete separable completeRead ->
        Cont completeRead stream denseRead ->
          Cont denseRead readback rowRead ->
            PkgSig bundle provenance pkg ->
              PkgSig bundle localName pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row rowRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                        hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                          hsame row rowRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory completeRead ∧ UnaryHistory denseRead ∧
                    UnaryHistory rowRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completeSeparableRead completeStreamDense denseReadbackRow provenancePkg
    localNamePkg
  obtain ⟨_metricUnary, completeUnary, separableUnary, streamUnary, readbackUnary,
    _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _metricCompleteLedger, _ledgerStreamReadback, _transportReplayProvenance,
    _carrierPkg⟩ := carrier
  have completeReadUnary : UnaryHistory completeRead :=
    unary_cont_closed completeUnary separableUnary completeSeparableRead
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed completeReadUnary streamUnary completeStreamDense
  have rowReadUnary : UnaryHistory rowRead :=
    unary_cont_closed denseReadUnary readbackUnary denseReadbackRow
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rowRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row rowRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rowRead ⟨hsame_refl rowRead, rowReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, completeReadUnary, denseReadUnary, rowReadUnary⟩

end BEDC.Derived.PolishSpaceUp
