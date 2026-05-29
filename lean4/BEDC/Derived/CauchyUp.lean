import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Ask
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.Ask
open BEDC.FKernel.Package

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

theorem CauchySeedRealSealBoundary {W D R E toleranceRead readbackRead sealRead : BHist} :
    UnaryHistory W →
      UnaryHistory D →
        UnaryHistory R →
          UnaryHistory E →
            Cont W D toleranceRead →
              Cont toleranceRead R readbackRead →
                Cont readbackRead E sealRead →
                  UnaryHistory toleranceRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory sealRead ∧ Cont W D toleranceRead ∧
                      Cont toleranceRead R readbackRead ∧ Cont readbackRead E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro windowUnary toleranceUnary readbackUnary sealUnary windowToleranceRead
    toleranceReadbackRead readbackSealRead
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary toleranceUnary windowToleranceRead
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary readbackUnary toleranceReadbackRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealUnary readbackSealRead
  exact
    ⟨toleranceReadUnary, readbackReadUnary, sealReadUnary, windowToleranceRead,
      toleranceReadbackRead, readbackSealRead⟩

def CauchyModulusSpaceCarrier (I S W D R Q H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory I ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N

theorem CauchyModulusSpaceNameCertObligations [AskSetup] [PackageSetup]
    {I S W D R Q H C P N schedule readback route : BHist} :
    CauchyModulusSpaceCarrier I S W D R Q H C P N ->
      Cont S W schedule ->
        Cont D R readback ->
          Cont schedule readback route ->
            UnaryHistory schedule ∧ UnaryHistory readback ∧ UnaryHistory route := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory AskSetup PackageSetup
  intro carrier scheduleCont readbackCont routeCont
  obtain ⟨_iUnary, sUnary, wUnary, dUnary, rUnary, _qUnary, _hUnary, _cUnary,
    _pUnary, _nUnary⟩ := carrier
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed sUnary wUnary scheduleCont
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed dUnary rUnary readbackCont
  have routeUnary : UnaryHistory route :=
    unary_cont_closed scheduleUnary readbackUnary routeCont
  exact ⟨scheduleUnary, readbackUnary, routeUnary⟩

theorem CauchyRootUnaryAdmission [AskSetup] [PackageSetup]
    {stream request dyadic readback realSeal _transport _replay _provenance _localName tailRead
      toleranceRead realRead : BHist} :
    UnaryHistory stream -> UnaryHistory request -> UnaryHistory dyadic ->
      UnaryHistory readback -> UnaryHistory realSeal -> Cont stream request tailRead ->
        Cont tailRead dyadic toleranceRead -> Cont toleranceRead readback realRead ->
          UnaryHistory tailRead ∧ UnaryHistory toleranceRead ∧ UnaryHistory realRead ∧
            Cont stream request tailRead ∧ Cont tailRead dyadic toleranceRead ∧
              Cont toleranceRead readback realRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory AskSetup PackageSetup
  intro streamUnary requestUnary dyadicUnary readbackUnary _realSealUnary tailRoute
    toleranceRoute realRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed streamUnary requestUnary tailRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailReadUnary dyadicUnary toleranceRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed toleranceReadUnary readbackUnary realRoute
  exact
    ⟨tailReadUnary, toleranceReadUnary, realReadUnary, tailRoute, toleranceRoute,
      realRoute⟩

theorem CauchyRootFilterModulusCompatibility
    {S Q D R E H C P N streamRequest toleranceRead readbackRead sealRead
      structuralRead namedRead : BHist} :
    UnaryHistory S ->
      UnaryHistory Q ->
        UnaryHistory D ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont S Q streamRequest ->
                        Cont streamRequest D toleranceRead ->
                          Cont toleranceRead R readbackRead ->
                            Cont readbackRead E sealRead ->
                              Cont H C structuralRead ->
                                Cont P N namedRead ->
                                  UnaryHistory streamRequest ∧
                                    UnaryHistory toleranceRead ∧
                                      UnaryHistory readbackRead ∧
                                        UnaryHistory sealRead ∧
                                          UnaryHistory structuralRead ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary qUnary dUnary rUnary eUnary hUnary cUnary pUnary nUnary streamRoute
    toleranceRoute readbackRoute sealRoute structuralRoute namingRoute
  have streamRequestUnary : UnaryHistory streamRequest :=
    unary_cont_closed sUnary qUnary streamRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed streamRequestUnary dUnary toleranceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary rUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary eUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namingRoute
  exact
    ⟨streamRequestUnary, toleranceReadUnary, readbackReadUnary, sealReadUnary,
      structuralReadUnary, namedReadUnary⟩

end BEDC.Derived.CauchyUp
