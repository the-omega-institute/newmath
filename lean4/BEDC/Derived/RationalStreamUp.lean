import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalStreamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package

def RationalStreamPacket [AskSetup] [PackageSetup]
    (index schedule pointRows classifierRows transportRows contRows provenance nameRow window :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory pointRows ∧
    UnaryHistory classifierRows ∧ UnaryHistory transportRows ∧ Cont index schedule window ∧
      Cont window pointRows classifierRows ∧ Cont classifierRows transportRows contRows ∧
        Cont contRows provenance nameRow ∧ PkgSig bundle nameRow pkg

theorem RationalStreamPacket_finite_window_carrier_transport [AskSetup] [PackageSetup]
    {index schedule pointRows classifierRows transportRows contRows provenance nameRow window
      index' schedule' pointRows' classifierRows' transportRows' contRows' provenance' nameRow'
      window' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule pointRows classifierRows transportRows contRows provenance
      nameRow window bundle pkg →
      hsame index index' →
      hsame schedule schedule' →
      hsame pointRows pointRows' →
      hsame classifierRows classifierRows' →
      hsame transportRows transportRows' →
      hsame provenance provenance' →
      Cont index' schedule' window' →
      Cont window' pointRows' classifierRows' →
      Cont classifierRows' transportRows' contRows' →
      Cont contRows' provenance' nameRow' →
      PkgSig bundle nameRow' pkg →
      RationalStreamPacket index' schedule' pointRows' classifierRows' transportRows' contRows'
        provenance' nameRow' window' bundle pkg ∧ hsame nameRow nameRow' := by
  intro packet sameIndex sameSchedule samePointRows sameClassifierRows sameTransportRows
    sameProvenance newIndexSchedule newWindowPoint newClassifierTransport newNameCont newPkg
  cases packet with
  | intro indexUnary rest =>
      cases rest with
      | intro scheduleUnary rest =>
          cases rest with
          | intro pointRowsUnary rest =>
              cases rest with
              | intro classifierRowsUnary rest =>
                  cases rest with
                  | intro transportRowsUnary rest =>
                      cases rest with
                      | intro _oldIndexSchedule rest =>
                          cases rest with
                          | intro _oldWindowPoint rest =>
                              cases rest with
                              | intro oldClassifierTransport rest =>
                                  cases rest with
                                  | intro oldNameCont _oldPkg =>
                                      have sameContRows : hsame contRows contRows' :=
                                        cont_respects_hsame sameClassifierRows sameTransportRows
                                          oldClassifierTransport newClassifierTransport
                                      have sameNameRow : hsame nameRow nameRow' :=
                                        cont_respects_hsame sameContRows sameProvenance oldNameCont
                                          newNameCont
                                      exact And.intro
                                        (And.intro
                                          (unary_transport indexUnary sameIndex)
                                          (And.intro
                                            (unary_transport scheduleUnary sameSchedule)
                                            (And.intro
                                              (unary_transport pointRowsUnary samePointRows)
                                              (And.intro
                                                (unary_transport classifierRowsUnary
                                                  sameClassifierRows)
                                                (And.intro
                                                  (unary_transport transportRowsUnary
                                                    sameTransportRows)
                                                  (And.intro newIndexSchedule
                                                    (And.intro newWindowPoint
                                                      (And.intro newClassifierTransport
                                                        (And.intro newNameCont newPkg)))))))))
                                        sameNameRow

end BEDC.Derived.RationalStreamUp
