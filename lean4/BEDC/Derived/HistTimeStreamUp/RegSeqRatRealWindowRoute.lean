import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_regseq_real_window_route [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow regseqRead realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay streamWindow →
        Cont streamWindow transport regseqRead →
          Cont regseqRead provenance realRead →
            PkgSig bundle regseqRead pkg →
              PkgSig bundle realRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      HistTimeStreamCarrier source schedule start replay transport provenance name
                        bundle pkg ∧ hsame row realRead)
                    (fun row : BHist => UnaryHistory row ∧ hsame row realRead)
                    (fun _row : BHist =>
                      Cont source replay streamWindow ∧
                        Cont streamWindow transport regseqRead ∧
                          Cont regseqRead provenance realRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle regseqRead pkg ∧
                              PkgSig bundle realRead pkg)
                    hsame ∧
                  UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
                    UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayWindow windowTransportRegseq regseqProvenanceReal regseqPkg
    realPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, transportUnary,
    provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamWindowUnary transportUnary windowTransportRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary provenanceUnary regseqProvenanceReal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row realRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row realRead)
          (fun _row : BHist =>
            Cont source replay streamWindow ∧
              Cont streamWindow transport regseqRead ∧
                Cont regseqRead provenance realRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle regseqRead pkg ∧
                    PkgSig bundle realRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realRead ⟨carrierWitness, hsame_refl realRead⟩
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
        intro row sourceRow
        exact ⟨unary_transport_symm realReadUnary sourceRow.right, sourceRow.right⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayWindow, windowTransportRegseq, regseqProvenanceReal, provenancePkg,
            regseqPkg, realPkg⟩
    }
  exact ⟨cert, streamWindowUnary, regseqReadUnary, realReadUnary⟩

end BEDC.Derived.HistTimeStreamUp
