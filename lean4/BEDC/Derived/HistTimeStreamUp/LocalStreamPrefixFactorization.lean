import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_local_stream_prefix_factorization [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow regseqRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay streamWindow →
        Cont streamWindow transport regseqRead →
          Cont regseqRead provenance realRead →
            PkgSig bundle realRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    HistTimeStreamCarrier source schedule start replay transport provenance name
                      bundle pkg ∧ hsame row streamWindow)
                  (fun row : BHist => UnaryHistory row ∧ hsame row streamWindow)
                  (fun _row : BHist =>
                    Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead ∧
                      Cont regseqRead provenance realRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle realRead pkg)
                  hsame ∧
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
                UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead ∧
                Cont regseqRead provenance realRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sourceReplayWindow windowTransportRegseq regseqProvenanceReal realPkg
  have carrierPacket :
      HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg :=
    carrier
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary, provenanceUnary,
    _nameUnary, _scheduleStartReplay, _sourceReplayProvenance, _provenanceReplay,
    provenancePkg, _namePkg⟩ := carrier
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamWindowUnary transportUnary windowTransportRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary provenanceUnary regseqProvenanceReal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name bundle
              pkg ∧ hsame row streamWindow)
          (fun row : BHist => UnaryHistory row ∧ hsame row streamWindow)
          (fun _row : BHist =>
            Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead ∧
              Cont regseqRead provenance realRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle realRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro streamWindow ⟨carrierPacket, hsame_refl streamWindow⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨unary_transport streamWindowUnary (hsame_symm source.right), source.right⟩
    · intro _row _source
      exact
        ⟨sourceReplayWindow, windowTransportRegseq, regseqProvenanceReal, provenancePkg, realPkg⟩
  exact
    ⟨cert, sourceUnary, scheduleUnary, startUnary, streamWindowUnary, regseqUnary, realUnary,
      sourceReplayWindow, windowTransportRegseq, regseqProvenanceReal, provenancePkg, realPkg⟩

end BEDC.Derived.HistTimeStreamUp
