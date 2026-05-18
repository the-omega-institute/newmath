import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_real_readback_scope_lock [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow regseqRead realRead
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay streamWindow ->
        Cont streamWindow transport regseqRead ->
          Cont streamWindow name regseqRead ->
            Cont regseqRead provenance realRead ->
              Cont regseqRead provenance readback ->
                PkgSig bundle realRead pkg ->
                  PkgSig bundle readback pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          HistTimeStreamCarrier source schedule start replay transport provenance
                            name bundle pkg ∧ hsame row readback)
                        (fun row : BHist =>
                          UnaryHistory row ∧
                            (hsame row streamWindow ∨ hsame row regseqRead ∨
                              hsame row realRead ∨ hsame row readback))
                        (fun _row : BHist =>
                          Cont source replay streamWindow ∧
                            Cont streamWindow transport regseqRead ∧
                              Cont streamWindow name regseqRead ∧
                                Cont regseqRead provenance readback ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle readback pkg)
                        hsame ∧
                      hsame realRead readback ∧ UnaryHistory streamWindow ∧
                        UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                          UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayWindow windowTransportRegseq windowNameRegseq
    regseqProvenanceReal regseqProvenanceReadback _realPkg readbackPkg
  have carrierWitness := carrier
  obtain
    ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, transportUnary, provenanceUnary,
      _nameUnary, _scheduleStartReplay, _sourceReplayProvenance, _provenanceReplay,
      provenancePkg, _namePkg⟩ := carrier
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamWindowUnary transportUnary windowTransportRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary provenanceUnary regseqProvenanceReal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed regseqReadUnary provenanceUnary regseqProvenanceReadback
  have realReadSameReadback : hsame realRead readback :=
    cont_deterministic regseqProvenanceReal regseqProvenanceReadback
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name bundle
              pkg ∧ hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row streamWindow ∨ hsame row regseqRead ∨ hsame row realRead ∨
                hsame row readback))
          (fun _row : BHist =>
            Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead ∧
              Cont streamWindow name regseqRead ∧ Cont regseqRead provenance readback ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro readback
          ⟨carrierWitness, hsame_refl readback⟩
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
        exact
          ⟨unary_transport_symm readbackUnary sourceRow.right,
            Or.inr (Or.inr (Or.inr sourceRow.right))⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayWindow, windowTransportRegseq, windowNameRegseq,
            regseqProvenanceReadback, provenancePkg, readbackPkg⟩
    }
  exact
    ⟨cert, realReadSameReadback, streamWindowUnary, regseqReadUnary, realReadUnary,
      readbackUnary⟩

end BEDC.Derived.HistTimeStreamUp
