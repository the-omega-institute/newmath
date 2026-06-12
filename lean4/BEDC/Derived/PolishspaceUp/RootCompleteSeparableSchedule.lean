import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceRootCompleteSeparableSchedule [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionSchedule separableSchedule completeSeparableSchedule : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier metric complete separable stream readback
        ledger transport replay provenance localName bundle pkg ->
      Cont metric complete completionSchedule ->
        Cont separable stream separableSchedule ->
          Cont completionSchedule separableSchedule completeSeparableSchedule ->
            PkgSig bundle completeSeparableSchedule pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row completionSchedule ∨ hsame row separableSchedule ∨
                        hsame row completeSeparableSchedule) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                      hsame row stream ∨ hsame row completionSchedule ∨
                        hsame row separableSchedule ∨ hsame row completeSeparableSchedule)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle completeSeparableSchedule pkg)
                  hsame ∧ UnaryHistory completionSchedule ∧ UnaryHistory separableSchedule ∧
                UnaryHistory completeSeparableSchedule := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute separableRoute completeSeparableRoute completeSeparablePkg
  obtain ⟨metricUnary, completeUnary, separableUnary, streamUnary, _readbackUnary,
    _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _metricCompleteLedger, _ledgerStreamReadback, _transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have completionUnary : UnaryHistory completionSchedule :=
    unary_cont_closed metricUnary completeUnary completionRoute
  have separableScheduleUnary : UnaryHistory separableSchedule :=
    unary_cont_closed separableUnary streamUnary separableRoute
  have completeSeparableUnary : UnaryHistory completeSeparableSchedule :=
    unary_cont_closed completionUnary separableScheduleUnary completeSeparableRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row completionSchedule ∨ hsame row separableSchedule ∨
                hsame row completeSeparableSchedule) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row completionSchedule ∨
                hsame row separableSchedule ∨ hsame row completeSeparableSchedule)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle completeSeparableSchedule pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completeSeparableSchedule
          ⟨Or.inr (Or.inr (hsame_refl completeSeparableSchedule)),
            completeSeparableUnary⟩
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
        have sourceRoute :
            hsame _other completionSchedule ∨ hsame _other separableSchedule ∨
              hsame _other completeSeparableSchedule := by
          cases source.left with
          | inl completionSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) completionSame)
          | inr tail =>
              cases tail with
              | inl separableSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) separableSame))
              | inr completeSeparableSame =>
                  exact
                    Or.inr
                      (Or.inr (hsame_trans (hsame_symm sameRows) completeSeparableSame))
        exact ⟨sourceRoute, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl completionSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl completionSame))))
      | inr tail =>
          cases tail with
          | inl separableSame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl separableSame)))))
          | inr completeSeparableSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr completeSeparableSame)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, completeSeparablePkg⟩
  }
  exact ⟨cert, completionUnary, separableScheduleUnary, completeSeparableUnary⟩

end BEDC.Derived.PolishspaceUp
