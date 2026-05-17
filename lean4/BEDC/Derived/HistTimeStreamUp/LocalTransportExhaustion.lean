import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_local_transport_exhaustion [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint transported replayed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay endpoint →
        hsame endpoint transported →
          Cont transported schedule replayed →
            PkgSig bundle replayed pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    HistTimeStreamCarrier source schedule start replay transport provenance name
                      bundle pkg ∧ hsame row replayed)
                  (fun row : BHist =>
                    UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory transported ∧
                      UnaryHistory replayed ∧ hsame row replayed)
                  (fun _row : BHist =>
                    Cont source replay endpoint ∧ Cont transported schedule replayed ∧
                      hsame endpoint transported ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle replayed pkg)
                  hsame ∧
                UnaryHistory replayed ∧ hsame endpoint provenance := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayEndpoint endpointTransported transportedScheduleReplayed replayedPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary replayUnary sourceReplayEndpoint
  have transportedUnary : UnaryHistory transported :=
    unary_transport endpointUnary endpointTransported
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary scheduleUnary transportedScheduleReplayed
  have endpointSameProvenance : hsame endpoint provenance :=
    cont_deterministic sourceReplayEndpoint sourceReplayProvenance
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row replayed)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro replayed
        (And.intro carrierWitness (hsame_refl replayed))
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
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row replayed)
          (fun row : BHist =>
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory transported ∧
              UnaryHistory replayed ∧ hsame row replayed)
          (fun _row : BHist =>
            Cont source replay endpoint ∧ Cont transported schedule replayed ∧
              hsame endpoint transported ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle replayed pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceUnary, scheduleUnary, transportedUnary, replayedUnary, sourceRow.right⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayEndpoint, transportedScheduleReplayed, endpointTransported, provenancePkg,
            replayedPkg⟩
    }
  exact And.intro semantic (And.intro replayedUnary endpointSameProvenance)

end BEDC.Derived.HistTimeStreamUp
