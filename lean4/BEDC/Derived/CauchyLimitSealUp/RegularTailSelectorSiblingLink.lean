import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_regular_tail_selector_sibling_link [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint
      selectorTail selectorSupport tailMeet publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg ->
      Cont source schedule selectorTail ->
        Cont selectorTail dyadic selectorSupport ->
          Cont selectorSupport sealRow tailMeet ->
            Cont tailMeet endpoint publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory selectorTail /\ UnaryHistory selectorSupport /\
                  UnaryHistory tailMeet /\ UnaryHistory publicRead /\
                    Cont source schedule selectorTail /\
                      Cont selectorTail dyadic selectorSupport /\
                        Cont selectorSupport sealRow tailMeet /\
                          Cont tailMeet endpoint publicRead /\
                            PkgSig bundle endpoint pkg /\ PkgSig bundle publicRead pkg /\
                              hsame endpoint (append provenance localCert) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceScheduleTail tailDyadicSupport supportSealMeet meetEndpointPublic
    publicPkg
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, _diagonalUnary, sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have selectorTailUnary : UnaryHistory selectorTail :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have selectorSupportUnary : UnaryHistory selectorSupport :=
    unary_cont_closed selectorTailUnary dyadicUnary tailDyadicSupport
  have tailMeetUnary : UnaryHistory tailMeet :=
    unary_cont_closed selectorSupportUnary sealUnary supportSealMeet
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed tailMeetUnary endpointUnary meetEndpointPublic
  exact
    ⟨selectorTailUnary, selectorSupportUnary, tailMeetUnary, publicReadUnary,
      sourceScheduleTail, tailDyadicSupport, supportSealMeet, meetEndpointPublic,
      endpointPkg, publicPkg, sameEndpoint⟩

end BEDC.Derived.CauchyLimitSealUp
