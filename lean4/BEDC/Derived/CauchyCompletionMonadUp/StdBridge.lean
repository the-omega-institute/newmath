import BEDC.Derived.CauchyCompletionMonadUp

namespace BEDC.Derived.CauchyCompletionMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMonadUp_StdBridge [AskSetup] [PackageSetup]
    {sourceFamily windows observations schedule diagonal sealRow transport route nameRow
      standardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadPacket sourceFamily windows observations schedule diagonal sealRow
        transport route nameRow bundle pkg ->
      Cont sealRow route standardRead ->
        PkgSig bundle standardRead pkg ->
          UnaryHistory observations ∧ UnaryHistory sealRow ∧ UnaryHistory route ∧
            UnaryHistory standardRead ∧ hsame observations (append schedule windows) ∧
              hsame sealRow (append observations diagonal) ∧
                hsame route (append sealRow transport) ∧
                  hsame standardRead (append sealRow route) ∧
                    Cont sealRow route standardRead ∧ PkgSig bundle sealRow pkg ∧
                      PkgSig bundle standardRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory hsame
  intro packet sealRouteStandard standardPkg
  obtain ⟨_sourceFamilyUnary, windowsUnary, scheduleUnary, diagonalUnary, transportUnary,
    _nameRowUnary, scheduleWindowsObservations, observationsDiagonalSealRow,
    sealRowTransportRoute, _routeNameSealRow, sealRowPkg⟩ := packet
  have observationsUnary : UnaryHistory observations :=
    unary_cont_closed scheduleUnary windowsUnary scheduleWindowsObservations
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed observationsUnary diagonalUnary observationsDiagonalSealRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed sealRowUnary transportUnary sealRowTransportRoute
  have standardUnary : UnaryHistory standardRead :=
    unary_cont_closed sealRowUnary routeUnary sealRouteStandard
  exact
    ⟨observationsUnary, sealRowUnary, routeUnary, standardUnary,
      scheduleWindowsObservations, observationsDiagonalSealRow, sealRowTransportRoute,
      sealRouteStandard, sealRouteStandard, sealRowPkg, standardPkg⟩

end BEDC.Derived.CauchyCompletionMonadUp
