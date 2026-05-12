import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalStreamPacket [AskSetup] [PackageSetup]
    (index schedule pointRows classifierRows transportRows contRows provenance nameRow window :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory pointRows ∧
    UnaryHistory classifierRows ∧ UnaryHistory transportRows ∧ Cont index schedule window ∧
      Cont window pointRows classifierRows ∧ Cont classifierRows transportRows contRows ∧
        Cont contRows provenance nameRow ∧ PkgSig bundle nameRow pkg

theorem RationalStreamPacket_schedule_transport_exactness [AskSetup] [PackageSetup]
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
        provenance' nameRow' window' bundle pkg ∧
        hsame window window' ∧ hsame contRows contRows' ∧ hsame nameRow nameRow' := by
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
                      | intro oldIndexSchedule rest =>
                          cases rest with
                          | intro oldWindowPoint rest =>
                              cases rest with
                              | intro oldClassifierTransport rest =>
                                  cases rest with
                                  | intro oldNameCont _oldPkg =>
                                      have sameWindow : hsame window window' :=
                                        cont_respects_hsame sameIndex sameSchedule
                                          oldIndexSchedule newIndexSchedule
                                      have sameClassifierRowsFromWindow :
                                          hsame classifierRows classifierRows' :=
                                        cont_respects_hsame sameWindow samePointRows oldWindowPoint
                                          newWindowPoint
                                      have sameContRows : hsame contRows contRows' :=
                                        cont_respects_hsame sameClassifierRows sameTransportRows
                                          oldClassifierTransport newClassifierTransport
                                      have sameNameRow : hsame nameRow nameRow' :=
                                        cont_respects_hsame sameContRows sameProvenance oldNameCont
                                          newNameCont
                                      have transported :
                                          RationalStreamPacket index' schedule' pointRows'
                                            classifierRows' transportRows' contRows' provenance'
                                            nameRow' window' bundle pkg :=
                                        ⟨unary_transport indexUnary sameIndex,
                                          unary_transport scheduleUnary sameSchedule,
                                          unary_transport pointRowsUnary samePointRows,
                                          unary_transport classifierRowsUnary sameClassifierRows,
                                          unary_transport transportRowsUnary sameTransportRows,
                                          newIndexSchedule,
                                          newWindowPoint,
                                          newClassifierTransport,
                                          newNameCont,
                                          newPkg⟩
                                      exact And.intro transported
                                        (And.intro sameWindow
                                          (And.intro sameContRows sameNameRow))

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
  have transported :=
    RationalStreamPacket_schedule_transport_exactness packet sameIndex sameSchedule samePointRows
      sameClassifierRows sameTransportRows sameProvenance newIndexSchedule newWindowPoint
      newClassifierTransport newNameCont newPkg
  exact And.intro transported.left transported.right.right.right

end BEDC.Derived.RationalStreamUp
