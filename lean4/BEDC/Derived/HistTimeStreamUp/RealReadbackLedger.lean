import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_real_readback_ledger [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow regseqRead realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay streamWindow →
        Cont streamWindow transport regseqRead →
          Cont regseqRead provenance realRead →
            PkgSig bundle realRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    HistTimeStreamCarrier source schedule start replay transport provenance name
                      bundle pkg ∧ hsame row realRead)
                  (fun row : BHist => UnaryHistory row ∧ hsame row realRead)
                  (fun _row : BHist =>
                    Cont source replay streamWindow ∧
                      Cont streamWindow transport regseqRead ∧
                        Cont regseqRead provenance realRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle realRead pkg)
                  hsame ∧
                UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayWindow windowTransportRegseq regseqProvenanceReal realPkg
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
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row realRead)
        hsame := by
    exact {
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
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name bundle
              pkg ∧ hsame row realRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row realRead)
          (fun _row : BHist =>
            Cont source replay streamWindow ∧
              Cont streamWindow transport regseqRead ∧
                Cont regseqRead provenance realRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle realRead pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport_symm realReadUnary sourceRow.right
        exact And.intro rowUnary sourceRow.right
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayWindow, windowTransportRegseq, regseqProvenanceReal, provenancePkg,
            realPkg⟩
    }
  exact
    ⟨semantic, streamWindowUnary, regseqReadUnary, realReadUnary, provenancePkg, realPkg⟩

end BEDC.Derived.HistTimeStreamUp
