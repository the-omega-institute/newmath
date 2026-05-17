import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_finite_window_readback_exhaustion [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow regseqRead realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay streamWindow ->
        Cont streamWindow transport regseqRead ->
          Cont regseqRead provenance realRead ->
            PkgSig bundle realRead pkg ->
              UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                Cont source replay streamWindow ∧ Cont streamWindow transport regseqRead ∧
                  Cont regseqRead provenance realRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceReplayWindow windowTransportRegseq regseqProvenanceReal realPkg
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, transportUnary,
    provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamWindowUnary transportUnary windowTransportRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary provenanceUnary regseqProvenanceReal
  exact
    ⟨streamWindowUnary, regseqReadUnary, realReadUnary, sourceReplayWindow,
      windowTransportRegseq, regseqProvenanceReal, provenancePkg, realPkg⟩

end BEDC.Derived.HistTimeStreamUp
