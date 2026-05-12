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
    UnaryHistory classifierRows ∧ UnaryHistory transportRows ∧ UnaryHistory provenance ∧
      Cont index schedule window ∧ Cont window pointRows classifierRows ∧
        Cont classifierRows transportRows contRows ∧ Cont contRows provenance nameRow ∧
          PkgSig bundle nameRow pkg

theorem RationalStreamPacket_common_denominator_window_exhaustion [AskSetup] [PackageSetup]
    {index schedule pointRows classifierRows transportRows contRows provenance nameRow window :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule pointRows classifierRows transportRows contRows provenance
      nameRow window bundle pkg →
      UnaryHistory window ∧ UnaryHistory classifierRows ∧ UnaryHistory contRows ∧
        UnaryHistory nameRow ∧ Cont index schedule window ∧ Cont window pointRows classifierRows ∧
          Cont classifierRows transportRows contRows ∧ Cont contRows provenance nameRow ∧
            PkgSig bundle nameRow pkg := by
  intro packet
  obtain ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, transportRowsUnary,
    provenanceUnary, windowRow, classifierRowsRow, contRowsRow, nameRowRow, pkgRow⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed indexUnary scheduleUnary windowRow
  have contRowsUnary : UnaryHistory contRows :=
    unary_cont_closed classifierRowsUnary transportRowsUnary contRowsRow
  have nameRowUnary : UnaryHistory nameRow :=
    unary_cont_closed contRowsUnary provenanceUnary nameRowRow
  exact
    ⟨windowUnary, classifierRowsUnary, contRowsUnary, nameRowUnary, windowRow,
      classifierRowsRow, contRowsRow, nameRowRow, pkgRow⟩

def RationalStreamSchedulePacket [AskSetup] [PackageSetup]
    (index schedule rational classifier transport route provenance registration
      scheduleWindow pointWindow packet : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory rational ∧
    UnaryHistory classifier ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory registration ∧
        Cont index schedule scheduleWindow ∧ Cont rational classifier pointWindow ∧
          Cont scheduleWindow pointWindow packet ∧ PkgSig bundle packet pkg

theorem RationalStreamSchedule_transport_exactness [AskSetup] [PackageSetup]
    {index schedule rational classifier transport route provenance registration scheduleWindow
      pointWindow packet index' schedule' rational' classifier' scheduleWindow' pointWindow'
      packet' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamSchedulePacket index schedule rational classifier transport route provenance
        registration scheduleWindow pointWindow packet bundle pkg ->
      hsame index index' -> hsame schedule schedule' -> hsame rational rational' ->
        hsame classifier classifier' -> Cont index' schedule' scheduleWindow' ->
          Cont rational' classifier' pointWindow' ->
            Cont scheduleWindow' pointWindow' packet' -> PkgSig bundle packet' pkg ->
              RationalStreamSchedulePacket index' schedule' rational' classifier' transport route
                  provenance registration scheduleWindow' pointWindow' packet' bundle pkg ∧
                hsame scheduleWindow scheduleWindow' ∧ hsame pointWindow pointWindow' ∧
                  hsame packet packet' := by
  intro packetData sameIndex sameSchedule sameRational sameClassifier scheduleWindowRow'
    pointWindowRow' packetRow' packetSig'
  obtain ⟨indexUnary, scheduleUnary, rationalUnary, classifierUnary, transportUnary,
    routeUnary, provenanceUnary, registrationUnary, scheduleWindowRow, pointWindowRow,
    packetRow, _packetSig⟩ := packetData
  have sameScheduleWindow : hsame scheduleWindow scheduleWindow' :=
    cont_respects_hsame sameIndex sameSchedule scheduleWindowRow scheduleWindowRow'
  have samePointWindow : hsame pointWindow pointWindow' :=
    cont_respects_hsame sameRational sameClassifier pointWindowRow pointWindowRow'
  have samePacket : hsame packet packet' :=
    cont_respects_hsame sameScheduleWindow samePointWindow packetRow packetRow'
  have transported :
      RationalStreamSchedulePacket index' schedule' rational' classifier' transport route
          provenance registration scheduleWindow' pointWindow' packet' bundle pkg :=
    ⟨unary_transport indexUnary sameIndex,
      unary_transport scheduleUnary sameSchedule,
      unary_transport rationalUnary sameRational,
      unary_transport classifierUnary sameClassifier,
      transportUnary,
      routeUnary,
      provenanceUnary,
      registrationUnary,
      scheduleWindowRow',
      pointWindowRow',
      packetRow',
      packetSig'⟩
  exact ⟨transported, sameScheduleWindow, samePointWindow, samePacket⟩

theorem RationalStreamPacket_pointwise_rat_obligations [AskSetup] [PackageSetup]
    {index schedule pointRows classifierRows transportRows contRows provenance nameRow window :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule pointRows classifierRows transportRows contRows provenance
        nameRow window bundle pkg ->
      UnaryHistory index ∧ UnaryHistory pointRows ∧ UnaryHistory classifierRows ∧
        Cont window pointRows classifierRows ∧
          Cont contRows provenance nameRow ∧ PkgSig bundle nameRow pkg := by
  intro packet
  obtain ⟨indexUnary, _scheduleUnary, pointRowsUnary, classifierRowsUnary, _transportRowsUnary,
    _provenanceUnary, _indexScheduleRow, windowPointRow, _classifierTransportRow, nameRowRow,
    pkgSig⟩ := packet
  exact ⟨indexUnary, pointRowsUnary, classifierRowsUnary, windowPointRow, nameRowRow, pkgSig⟩

theorem RationalStreamPacket_regseqrat_finite_window_surface [AskSetup] [PackageSetup]
    {index schedule pointRows classifierRows transportRows contRows provenance nameRow window
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule pointRows classifierRows transportRows contRows provenance
        nameRow window bundle pkg ->
      UnaryHistory nameRow ->
      Cont window nameRow consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory pointRows ∧
            UnaryHistory classifierRows ∧ UnaryHistory window ∧ UnaryHistory consumer ∧
              Cont index schedule window ∧ Cont window nameRow consumer ∧
                PkgSig bundle consumer pkg := by
  intro packet nameRowUnary consumerRow consumerPkg
  obtain ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, _transportRowsUnary,
    _provenanceUnary, indexScheduleRow, _windowPointRow, _classifierTransportRow, _nameRow,
    _namePkg⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed indexUnary scheduleUnary indexScheduleRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary nameRowUnary consumerRow
  exact
    ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, windowUnary,
      consumerUnary, indexScheduleRow, consumerRow, consumerPkg⟩

theorem RationalStreamPacket_common_window_classifier_stability [AskSetup] [PackageSetup]
    {index schedule pointRows classifierRows transportRows contRows provenance nameRow window
      commonWindow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule pointRows classifierRows transportRows contRows provenance
        nameRow window bundle pkg ->
      UnaryHistory commonWindow ->
        Cont window commonWindow consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory pointRows ∧
              UnaryHistory classifierRows ∧ UnaryHistory window ∧ UnaryHistory commonWindow ∧
                UnaryHistory consumer ∧ Cont index schedule window ∧
                  Cont window commonWindow consumer ∧ PkgSig bundle consumer pkg := by
  intro packet commonWindowUnary consumerRow consumerPkg
  obtain ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, _transportRowsUnary,
    _provenanceUnary, indexScheduleRow, _windowPointRow, _classifierTransportRow, _nameRow,
    _namePkg⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed indexUnary scheduleUnary indexScheduleRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary commonWindowUnary consumerRow
  exact
    ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, windowUnary,
      commonWindowUnary, consumerUnary, indexScheduleRow, consumerRow, consumerPkg⟩

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
  obtain ⟨indexUnary, scheduleUnary, pointRowsUnary, classifierRowsUnary, transportRowsUnary,
    provenanceUnary, oldIndexSchedule, _oldWindowPoint, oldClassifierTransport, oldNameCont,
    _oldPkg⟩ := packet
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameIndex sameSchedule oldIndexSchedule newIndexSchedule
  have sameContRows : hsame contRows contRows' :=
    cont_respects_hsame sameClassifierRows sameTransportRows oldClassifierTransport
      newClassifierTransport
  have sameNameRow : hsame nameRow nameRow' :=
    cont_respects_hsame sameContRows sameProvenance oldNameCont newNameCont
  have transported :
      RationalStreamPacket index' schedule' pointRows' classifierRows' transportRows' contRows'
        provenance' nameRow' window' bundle pkg :=
    ⟨unary_transport indexUnary sameIndex,
      unary_transport scheduleUnary sameSchedule,
      unary_transport pointRowsUnary samePointRows,
      unary_transport classifierRowsUnary sameClassifierRows,
      unary_transport transportRowsUnary sameTransportRows,
      unary_transport provenanceUnary sameProvenance,
      newIndexSchedule,
      newWindowPoint,
      newClassifierTransport,
      newNameCont,
      newPkg⟩
  exact And.intro transported (And.intro sameWindow (And.intro sameContRows sameNameRow))

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
