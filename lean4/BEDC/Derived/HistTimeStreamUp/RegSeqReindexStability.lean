import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_regseq_reindex_stability [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name window transportedWindow regseqInput
      realReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay window →
        hsame window transportedWindow →
          Cont transportedWindow schedule regseqInput →
            Cont regseqInput provenance realReadback →
              PkgSig bundle regseqInput pkg →
                PkgSig bundle realReadback pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        HistTimeStreamCarrier source schedule start replay transport provenance name
                          bundle pkg ∧ hsame row realReadback)
                      (fun row : BHist =>
                        UnaryHistory transportedWindow ∧ UnaryHistory regseqInput ∧
                          UnaryHistory realReadback ∧ hsame row realReadback)
                      (fun _row : BHist =>
                        Cont source replay window ∧
                          Cont transportedWindow schedule regseqInput ∧
                            Cont regseqInput provenance realReadback ∧
                              hsame window transportedWindow ∧ PkgSig bundle regseqInput pkg ∧
                                PkgSig bundle realReadback pkg)
                      hsame ∧
                    UnaryHistory regseqInput ∧ UnaryHistory realReadback := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayWindow sameWindow windowScheduleRegseq regseqProvenanceReal
    regseqPkg realPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, _startUnary, replayUnary, _transportUnary,
    provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have transportedWindowUnary : UnaryHistory transportedWindow :=
    unary_transport windowUnary sameWindow
  have regseqUnary : UnaryHistory regseqInput :=
    unary_cont_closed transportedWindowUnary scheduleUnary windowScheduleRegseq
  have realUnary : UnaryHistory realReadback :=
    unary_cont_closed regseqUnary provenanceUnary regseqProvenanceReal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row realReadback)
          (fun row : BHist =>
            UnaryHistory transportedWindow ∧ UnaryHistory regseqInput ∧
              UnaryHistory realReadback ∧ hsame row realReadback)
          (fun _row : BHist =>
            Cont source replay window ∧
              Cont transportedWindow schedule regseqInput ∧
                Cont regseqInput provenance realReadback ∧
                  hsame window transportedWindow ∧ PkgSig bundle regseqInput pkg ∧
                    PkgSig bundle realReadback pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realReadback ⟨carrierWitness, hsame_refl realReadback⟩
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
          intro _row _other sameRows sourceRow
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨transportedWindowUnary, regseqUnary, realUnary, sourceRow.right⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayWindow, windowScheduleRegseq, regseqProvenanceReal, sameWindow,
            regseqPkg, realPkg⟩
    }
  exact ⟨cert, regseqUnary, realUnary⟩

end BEDC.Derived.HistTimeStreamUp
