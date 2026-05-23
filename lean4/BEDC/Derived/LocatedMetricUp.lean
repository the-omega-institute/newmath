import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedMetricCarrier [AskSetup] [PackageSetup]
    (point metric located stream regseq real separated transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory point ∧ UnaryHistory metric ∧ UnaryHistory located ∧
    UnaryHistory stream ∧ UnaryHistory regseq ∧ UnaryHistory real ∧
      UnaryHistory separated ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem LocatedMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {point metric located stream regseq real separated transport replay provenance name
      metricRead locatedRead regseqRead realRead separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedMetricCarrier point metric located stream regseq real separated transport replay
        provenance name bundle pkg →
      Cont point metric metricRead →
        Cont metric located locatedRead →
          Cont located stream regseqRead →
            Cont regseq real realRead →
              Cont real separated separatedRead →
                PkgSig bundle separatedRead pkg →
                  UnaryHistory metricRead ∧ UnaryHistory locatedRead ∧
                    UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                      UnaryHistory separatedRead ∧ Cont point metric metricRead ∧
                        Cont metric located locatedRead ∧ Cont located stream regseqRead ∧
                          Cont regseq real realRead ∧ Cont real separated separatedRead ∧
                              PkgSig bundle provenance pkg ∧
                              PkgSig bundle separatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier pointMetricRead metricLocatedRead locatedStreamRead regseqRealRead
    realSeparatedRead separatedPkg
  obtain ⟨pointUnary, metricUnary, locatedUnary, streamUnary, regseqUnary, realUnary,
    separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, provenancePkg, _namePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed pointUnary metricUnary pointMetricRead
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed metricUnary locatedUnary metricLocatedRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed locatedUnary streamUnary locatedStreamRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary realUnary regseqRealRead
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed realUnary separatedUnary realSeparatedRead
  exact
    ⟨metricReadUnary,
      locatedReadUnary,
      regseqReadUnary,
      realReadUnary,
      separatedReadUnary,
      pointMetricRead,
      metricLocatedRead,
      locatedStreamRead,
      regseqRealRead,
      realSeparatedRead,
      provenancePkg,
      separatedPkg⟩

theorem LocatedMetricCarrier_completion_handoff [AskSetup] [PackageSetup]
    {point metric located stream regseq real separated transport replay provenance name
      metricRead locatedRead regseqRead realRead separatedRead completionRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedMetricCarrier point metric located stream regseq real separated transport replay
        provenance name bundle pkg →
      Cont point metric metricRead →
        Cont metric located locatedRead →
          Cont located stream regseqRead →
            Cont regseq real realRead →
              Cont real separated separatedRead →
                Cont separatedRead provenance completionRead →
                  Cont completionRead name exportRead →
                    PkgSig bundle exportRead pkg →
                      UnaryHistory metricRead ∧ UnaryHistory locatedRead ∧
                        UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                          UnaryHistory separatedRead ∧ UnaryHistory completionRead ∧
                            UnaryHistory exportRead ∧ Cont separatedRead provenance completionRead ∧
                              Cont completionRead name exportRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier pointMetricRead metricLocatedRead locatedStreamRead regseqRealRead
    realSeparatedRead separatedProvenanceCompletion completionNameExport exportPkg
  obtain ⟨pointUnary, metricUnary, locatedUnary, streamUnary, regseqUnary, realUnary,
    separatedUnary, _transportUnary, _replayUnary, provenanceUnary, nameUnary,
    _transportReplayProvenance, provenancePkg, _namePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed pointUnary metricUnary pointMetricRead
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed metricUnary locatedUnary metricLocatedRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed locatedUnary streamUnary locatedStreamRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary realUnary regseqRealRead
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed realUnary separatedUnary realSeparatedRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedReadUnary provenanceUnary separatedProvenanceCompletion
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed completionReadUnary nameUnary completionNameExport
  exact
    ⟨metricReadUnary,
      locatedReadUnary,
      regseqReadUnary,
      realReadUnary,
      separatedReadUnary,
      completionReadUnary,
      exportReadUnary,
      separatedProvenanceCompletion,
      completionNameExport,
      provenancePkg,
      exportPkg⟩

theorem LocatedMetricCarrier_dyadic_radius_localization [AskSetup] [PackageSetup]
    {point metric located stream regseq real separated transport replay provenance name
      metricRead locatedRead regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedMetricCarrier point metric located stream regseq real separated transport replay
        provenance name bundle pkg →
      Cont point metric metricRead →
        Cont metric located locatedRead →
          Cont located stream regseqRead →
            UnaryHistory metricRead ∧ UnaryHistory locatedRead ∧ UnaryHistory regseqRead ∧
              Cont point metric metricRead ∧ Cont metric located locatedRead ∧
                Cont located stream regseqRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier pointMetricRead metricLocatedRead locatedStreamRead
  obtain ⟨pointUnary, metricUnary, locatedUnary, streamUnary, _regseqUnary, _realUnary,
    _separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, provenancePkg, _namePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed pointUnary metricUnary pointMetricRead
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed metricUnary locatedUnary metricLocatedRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed locatedUnary streamUnary locatedStreamRead
  exact
    ⟨metricReadUnary,
      locatedReadUnary,
      regseqReadUnary,
      pointMetricRead,
      metricLocatedRead,
      locatedStreamRead,
      provenancePkg⟩

end BEDC.Derived.LocatedMetricUp
