import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceDenseScheduleTransportObligation [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      denseRead transportedDense : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceCarrier metric complete separable stream readback ledger transport replay
        provenance localName bundle pkg →
      Cont metric separable denseRead →
        Cont denseRead transport transportedDense →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist => hsame row transportedDense ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row separable ∨ hsame row stream ∨
                    hsame row readback ∨ hsame row ledger ∨ hsame row denseRead ∨
                      hsame row transportedDense)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont denseRead transport transportedDense ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory denseRead ∧ UnaryHistory transportedDense := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute transportRoute provenancePkg
  obtain ⟨metricUnary, _completeUnary, separableUnary, _streamUnary, _readbackUnary,
    _ledgerUnary, transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _metricCompleteLedger, _ledgerStreamReadback, _transportReplayProvenance,
    _carrierPkg, _localPkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary separableUnary denseRoute
  have transportedUnary : UnaryHistory transportedDense :=
    unary_cont_closed denseUnary transportUnary transportRoute
  have sourceTransported :
      (fun row : BHist => hsame row transportedDense ∧ UnaryHistory row) transportedDense :=
    ⟨hsame_refl transportedDense, transportedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedDense ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row separable ∨ hsame row stream ∨
              hsame row readback ∨ hsame row ledger ∨ hsame row denseRead ∨
                hsame row transportedDense)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont denseRead transport transportedDense ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transportedDense sourceTransported
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, transportRoute, provenancePkg⟩
  }
  exact ⟨cert, denseUnary, transportedUnary⟩

end BEDC.Derived.PolishSpaceUp
