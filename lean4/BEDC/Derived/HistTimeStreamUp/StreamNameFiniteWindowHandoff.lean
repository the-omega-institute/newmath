import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_streamname_finite_window_handoff [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay streamWindow ->
        PkgSig bundle streamWindow pkg ->
          SemanticNameCert
              (fun row : BHist =>
                HistTimeStreamCarrier source schedule start replay transport provenance name
                  bundle pkg ∧ hsame row streamWindow)
              (fun row : BHist =>
                UnaryHistory row ∧ hsame row streamWindow ∧ Cont source replay streamWindow)
              (fun _row : BHist =>
                Cont schedule start replay ∧ hsame provenance replay ∧
                  PkgSig bundle streamWindow pkg)
              hsame ∧
            UnaryHistory streamWindow ∧ Cont schedule start replay ∧
              Cont source replay streamWindow ∧ hsame provenance replay ∧
                PkgSig bundle streamWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert UnaryHistory hsame Cont
  intro carrier sourceReplayWindow windowPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, scheduleStartReplay, _sourceReplayProvenance,
    provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have windowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row streamWindow)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro streamWindow
        (And.intro carrierWitness (hsame_refl streamWindow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name bundle
              pkg ∧ hsame row streamWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ hsame row streamWindow ∧ Cont source replay streamWindow)
          (fun _row : BHist =>
            Cont schedule start replay ∧ hsame provenance replay ∧
              PkgSig bundle streamWindow pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport windowUnary (hsame_symm sourceRow.right)
        exact And.intro rowUnary (And.intro sourceRow.right sourceReplayWindow)
      ledger_sound := by
        intro _row _sourceRow
        exact And.intro scheduleStartReplay (And.intro provenanceReplay windowPkg)
    }
  exact
    And.intro semantic
      (And.intro windowUnary
        (And.intro scheduleStartReplay
          (And.intro sourceReplayWindow (And.intro provenanceReplay windowPkg))))

end BEDC.Derived.HistTimeStreamUp
