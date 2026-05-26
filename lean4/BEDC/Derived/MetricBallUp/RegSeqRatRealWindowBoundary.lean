import BEDC.Derived.MetricBallUp.PositiveRadiusTransport

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBallCarrier_regseqrat_real_window_boundary [AskSetup] [PackageSetup]
    {X dist center radius positive member transport replay provenance nameRow regseqRead
      realSeal windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricBallCarrier X dist center radius positive member transport replay provenance nameRow
        bundle pkg ->
      Cont member regseqRead windowRead ->
        Cont windowRead realSeal replay ->
          PkgSig bundle realSeal pkg ->
            UnaryHistory member ∧ UnaryHistory regseqRead ∧ UnaryHistory windowRead ∧
              UnaryHistory realSeal ∧ Cont member regseqRead windowRead ∧
                Cont windowRead realSeal replay ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier memberRegseqWindow windowRealReplay realSealPkg
  obtain ⟨_xUnary, _distUnary, _centerUnary, _radiusUnary, _positiveUnary, memberUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameRowUnary, _positiveMemberRoute,
    _memberReplayRoute, provenancePkg, _nameRowPkg⟩ := carrier
  have realUnary : UnaryHistory realSeal :=
    unary_cont_right_factor windowRealReplay replayUnary
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_left_factor windowRealReplay replayUnary
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_right_factor memberRegseqWindow windowUnary
  exact
    ⟨memberUnary, regseqUnary, windowUnary, realUnary, memberRegseqWindow,
      windowRealReplay, provenancePkg, realSealPkg⟩

end BEDC.Derived.MetricBallUp
