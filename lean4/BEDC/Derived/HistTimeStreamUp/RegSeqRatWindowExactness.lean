import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_regseqrat_window_exactness [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay streamWindow →
        Cont streamWindow transport regseqRead →
          PkgSig bundle regseqRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row regseqRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ (hsame row streamWindow ∨ hsame row regseqRead))
                (fun _row : BHist =>
                  Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle regseqRead pkg)
                hsame ∧
              UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
                Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayWindow windowTransportRegseq regseqPkg
  have carrierWitness := carrier
  obtain
    ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, transportUnary, _provenanceUnary,
      _nameUnary, _scheduleStartReplay, _sourceReplayProvenance, _provenanceReplay,
      provenancePkg, _namePkg⟩ := carrier
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary transportUnary windowTransportRegseq
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row regseqRead)
          (fun row : BHist =>
            UnaryHistory row ∧ (hsame row streamWindow ∨ hsame row regseqRead))
          (fun _row : BHist =>
            Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle regseqRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro regseqRead
          ⟨carrierWitness, hsame_refl regseqRead⟩
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
        exact ⟨unary_transport_symm regseqUnary sourceRow.right, Or.inr sourceRow.right⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨sourceReplayWindow, windowTransportRegseq, provenancePkg, regseqPkg⟩
    }
  exact ⟨cert, streamUnary, regseqUnary, sourceReplayWindow, windowTransportRegseq⟩

end BEDC.Derived.HistTimeStreamUp
