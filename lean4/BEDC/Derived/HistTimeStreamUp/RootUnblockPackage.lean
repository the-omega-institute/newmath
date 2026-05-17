import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_namecert_root_unblock_package [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow regseqRead realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay streamWindow →
        Cont streamWindow schedule regseqRead →
          Cont regseqRead name realRead →
            PkgSig bundle streamWindow pkg →
              PkgSig bundle regseqRead pkg →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        HistTimeStreamCarrier source schedule start replay transport provenance
                          name bundle pkg ∧ hsame row realRead)
                      (fun row : BHist => UnaryHistory row ∧ hsame row realRead)
                      (fun _row : BHist =>
                        Cont source replay streamWindow ∧
                          Cont streamWindow schedule regseqRead ∧
                            Cont regseqRead name realRead ∧ PkgSig bundle streamWindow pkg ∧
                              PkgSig bundle regseqRead pkg ∧ PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
                      UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier sourceReplayWindow windowScheduleRegseq regseqNameReal streamPkg regseqPkg
    realPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamWindowUnary scheduleUnary windowScheduleRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary nameUnary regseqNameReal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row realRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row realRead)
          (fun _row : BHist =>
            Cont source replay streamWindow ∧ Cont streamWindow schedule regseqRead ∧
              Cont regseqRead name realRead ∧ PkgSig bundle streamWindow pkg ∧
                PkgSig bundle regseqRead pkg ∧ PkgSig bundle realRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realRead
          (And.intro carrierWitness (hsame_refl realRead))
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
      pattern_sound := by
        intro _row sourceRow
        exact And.intro (unary_transport realReadUnary (hsame_symm sourceRow.right))
          sourceRow.right
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayWindow, windowScheduleRegseq, regseqNameReal, streamPkg, regseqPkg,
            realPkg⟩
    }
  exact ⟨cert, streamWindowUnary, regseqReadUnary, realReadUnary⟩

end BEDC.Derived.HistTimeStreamUp
