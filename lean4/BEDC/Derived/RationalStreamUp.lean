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
    RationalStreamPacket index schedule rational classifier transport route provenance
        registration scheduleWindow pointWindow packet bundle pkg ->
      hsame index index' -> hsame schedule schedule' -> hsame rational rational' ->
        hsame classifier classifier' -> Cont index' schedule' scheduleWindow' ->
          Cont rational' classifier' pointWindow' ->
            Cont scheduleWindow' pointWindow' packet' -> PkgSig bundle packet' pkg ->
              RationalStreamPacket index' schedule' rational' classifier' transport route
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
      RationalStreamPacket index' schedule' rational' classifier' transport route provenance
          registration scheduleWindow' pointWindow' packet' bundle pkg :=
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

end BEDC.Derived.RationalStreamUp
