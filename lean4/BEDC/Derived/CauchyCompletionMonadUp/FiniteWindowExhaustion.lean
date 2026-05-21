import BEDC.Derived.CauchyCompletionMonadUp

namespace BEDC.Derived.CauchyCompletionMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMonadPacket_finite_window_exhaustion [AskSetup] [PackageSetup]
    {sourceFamily windows observations schedule diagonal sealRow transport route nameRow
      publicRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadPacket sourceFamily windows observations schedule diagonal sealRow
        transport route nameRow bundle pkg →
      Cont sealRow route publicRead →
        Cont publicRead nameRow completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory sourceFamily ∧ UnaryHistory observations ∧ UnaryHistory sealRow ∧
              UnaryHistory route ∧ UnaryHistory publicRead ∧ UnaryHistory completionRead ∧
                hsame observations (append schedule windows) ∧
                  hsame sealRow (append observations diagonal) ∧
                    hsame route (append sealRow transport) ∧
                      Cont sealRow route publicRead ∧ Cont publicRead nameRow completionRead ∧
                        PkgSig bundle sealRow pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro packet sealRoutePublic publicNameCompletion completionPkg
  obtain ⟨sourceFamilyUnary, windowsUnary, scheduleUnary, diagonalUnary, transportUnary,
    nameRowUnary, scheduleWindowsObservations, observationsDiagonalSealRow,
    sealTransportRoute, _routeNameSeal, sealRowPkg⟩ := packet
  have observationsUnary : UnaryHistory observations :=
    unary_cont_closed scheduleUnary windowsUnary scheduleWindowsObservations
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed observationsUnary diagonalUnary observationsDiagonalSealRow
  have routeUnary : UnaryHistory route :=
    unary_cont_closed sealRowUnary transportUnary sealTransportRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealRowUnary routeUnary sealRoutePublic
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed publicReadUnary nameRowUnary publicNameCompletion
  exact
    ⟨sourceFamilyUnary, observationsUnary, sealRowUnary, routeUnary, publicReadUnary,
      completionReadUnary, scheduleWindowsObservations, observationsDiagonalSealRow,
      sealTransportRoute, sealRoutePublic, publicNameCompletion, sealRowPkg, completionPkg⟩

end BEDC.Derived.CauchyCompletionMonadUp
