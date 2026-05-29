import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionLeftExactnessNameCertObligations
    {S U D K E H C P N sourceUnit denseKernel extension route : BHist} :
    UnaryHistory S ->
      UnaryHistory U ->
        UnaryHistory D ->
          UnaryHistory K ->
            UnaryHistory E ->
              Cont S U sourceUnit ->
                Cont D K denseKernel ->
                  Cont sourceUnit denseKernel extension ->
                    Cont extension E route ->
                      UnaryHistory sourceUnit ∧
                        UnaryHistory denseKernel ∧
                          UnaryHistory extension ∧
                            UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary unitUnary denseUnary kernelUnary extensionUnary
    sourceUnitRoute denseKernelRoute extensionRoute replayRoute
  have sourceUnitUnary : UnaryHistory sourceUnit :=
    unary_cont_closed sourceUnary unitUnary sourceUnitRoute
  have denseKernelUnary : UnaryHistory denseKernel :=
    unary_cont_closed denseUnary kernelUnary denseKernelRoute
  have extensionUnary' : UnaryHistory extension :=
    unary_cont_closed sourceUnitUnary denseKernelUnary extensionRoute
  have routeUnary : UnaryHistory route :=
    unary_cont_closed extensionUnary' extensionUnary replayRoute
  exact ⟨sourceUnitUnary, denseKernelUnary, extensionUnary', routeUnary⟩

theorem CauchyModulusSpaceFiniteRoute [AskSetup] [PackageSetup]
    {index schedule stream dyadic readback realSeal transport replay provenance localName
      route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory index ->
      UnaryHistory schedule ->
        UnaryHistory stream ->
          UnaryHistory dyadic ->
            UnaryHistory readback ->
              UnaryHistory realSeal ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    UnaryHistory provenance ->
                      UnaryHistory localName ->
                        Cont index schedule stream ->
                          Cont dyadic readback realSeal ->
                            Cont transport replay provenance ->
                              Cont stream realSeal route ->
                                PkgSig bundle provenance pkg ->
                                  PkgSig bundle localName pkg ->
                                    UnaryHistory route ∧ Cont stream realSeal route ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro _indexUnary _scheduleUnary streamUnary _dyadicUnary _readbackUnary realSealUnary
    _transportUnary _replayUnary _provenanceUnary _localNameUnary _indexScheduleStream
    _dyadicReadbackRealSeal _transportReplayProvenance streamRealSealRoute provenancePkg
    localNamePkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed streamUnary realSealUnary streamRealSealRoute
  exact ⟨routeUnary, streamRealSealRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.CauchyUp
