import BEDC.FKernel.Hist
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Ask
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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
            UnaryHistory schedule /\ UnaryHistory readback /\ UnaryHistory route := by
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

end BEDC.Derived.CauchyUp
