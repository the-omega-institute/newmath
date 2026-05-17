import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_streamname_schedule_classifier_boundary [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name schedule' start' endpoint endpoint'
      streamWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      hsame schedule schedule' →
        hsame start start' →
          Cont schedule start endpoint →
            Cont schedule' start' endpoint' →
              Cont source replay streamWindow →
                PkgSig bundle endpoint pkg →
                  PkgSig bundle streamWindow pkg →
                    SemanticNameCert
                          (fun row : BHist =>
                            HistTimeStreamCarrier source schedule start replay transport
                                provenance name bundle pkg ∧
                              hsame row endpoint')
                          (fun row : BHist =>
                            UnaryHistory row ∧ hsame row endpoint' ∧
                              Cont schedule' start' endpoint')
                          (fun _row : BHist =>
                            hsame endpoint endpoint' ∧ Cont source replay streamWindow ∧
                              PkgSig bundle streamWindow pkg)
                          hsame ∧
                      hsame endpoint endpoint' ∧ UnaryHistory endpoint ∧
                        UnaryHistory endpoint' ∧ UnaryHistory streamWindow ∧
                          Cont source replay streamWindow ∧
                            PkgSig bundle streamWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier scheduleSame startSame scheduleStartEndpoint schedule'Start'Endpoint'
    sourceReplayWindow _endpointPkg windowPkg
  have carrierWitness :
      HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg :=
    carrier
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame scheduleSame startSame scheduleStartEndpoint schedule'Start'Endpoint'
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed scheduleUnary startUnary scheduleStartEndpoint
  have endpoint'Unary : UnaryHistory endpoint' :=
    unary_transport endpointUnary endpointSame
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
                bundle pkg ∧
              hsame row endpoint')
          (fun row : BHist =>
            UnaryHistory row ∧ hsame row endpoint' ∧ Cont schedule' start' endpoint')
          (fun _row : BHist =>
            hsame endpoint endpoint' ∧ Cont source replay streamWindow ∧
              PkgSig bundle streamWindow pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro endpoint'
          ⟨carrierWitness, hsame_refl endpoint'⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport endpoint'Unary (hsame_symm source.right)
      exact ⟨rowUnary, source.right, schedule'Start'Endpoint'⟩
    · intro _row _source
      exact ⟨endpointSame, sourceReplayWindow, windowPkg⟩
  exact
    ⟨cert, endpointSame, endpointUnary, endpoint'Unary, streamWindowUnary,
      sourceReplayWindow, windowPkg⟩

end BEDC.Derived.HistTimeStreamUp
