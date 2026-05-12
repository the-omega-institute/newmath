import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StoppingTimeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StoppingTimeSourcePacket [AskSetup] [PackageSetup]
    (prob process filtration horizon witness transport routes provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prob ∧ UnaryHistory process ∧ UnaryHistory filtration ∧
    UnaryHistory horizon ∧ UnaryHistory witness ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ Cont prob process filtration ∧
        Cont filtration horizon witness ∧ Cont witness transport routes ∧
          Cont routes provenance prob ∧ PkgSig bundle provenance pkg

theorem StoppingTimeSourcePacket_prefix_transport [AskSetup] [PackageSetup]
    {prob process filtration horizon witness transport routes provenance prob' process'
      filtration' horizon' witness' transport' routes' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoppingTimeSourcePacket prob process filtration horizon witness transport routes provenance
        bundle pkg ->
      hsame prob prob' ->
        hsame process process' ->
          hsame filtration filtration' ->
            hsame horizon horizon' ->
              hsame witness witness' ->
                hsame routes routes' ->
                  hsame provenance provenance' ->
                    Cont prob' process' filtration' ->
                      Cont filtration' horizon' witness' ->
                        Cont witness' transport' routes' ->
                          Cont routes' provenance' prob' ->
                            StoppingTimeSourcePacket prob' process' filtration' horizon'
                                witness' transport' routes' provenance' bundle pkg ∧
                              hsame transport transport' := by
  intro packet sameProb sameProcess sameFiltration sameHorizon sameWitness sameRoutes
    sameProvenance filtrationRow' witnessRow' routesRow' probRow'
  obtain ⟨probUnary, processUnary, filtrationUnary, horizonUnary, witnessUnary,
    transportUnary, routesUnary, provenanceUnary, _filtrationRow, _witnessRow, routesRow,
    _probRow, pkgSig⟩ := packet
  have probUnary' : UnaryHistory prob' :=
    unary_transport probUnary sameProb
  have processUnary' : UnaryHistory process' :=
    unary_transport processUnary sameProcess
  have filtrationUnary' : UnaryHistory filtration' :=
    unary_transport filtrationUnary sameFiltration
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport horizonUnary sameHorizon
  have witnessUnary' : UnaryHistory witness' :=
    unary_transport witnessUnary sameWitness
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameTransport : hsame transport transport' := by
    cases sameWitness
    cases sameRoutes
    exact cont_left_cancel routesRow routesRow'
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  cases sameProvenance
  exact
    ⟨⟨probUnary', processUnary', filtrationUnary', horizonUnary', witnessUnary',
        transportUnary', routesUnary', provenanceUnary', filtrationRow', witnessRow',
        routesRow', probRow', pkgSig⟩,
      sameTransport⟩

theorem StoppingTimeSourcePacket_filtration_prefix_stability [AskSetup] [PackageSetup]
    {prob process filtration horizon witness transport routes provenance prefixEvent
      prefixRoute eventRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoppingTimeSourcePacket prob process filtration horizon witness transport routes
        provenance bundle pkg ->
      UnaryHistory prefixEvent ->
        Cont filtration prefixEvent prefixRoute ->
          Cont prefixRoute witness eventRead ->
            PkgSig bundle provenance pkg ->
              UnaryHistory prob ∧ UnaryHistory process ∧ UnaryHistory filtration ∧
                UnaryHistory witness ∧ UnaryHistory prefixEvent ∧ UnaryHistory prefixRoute ∧
                  UnaryHistory eventRead ∧ Cont filtration prefixEvent prefixRoute ∧
                    Cont prefixRoute witness eventRead ∧ PkgSig bundle provenance pkg := by
  intro packet prefixUnary prefixRow eventReadRow provenanceSig
  obtain ⟨probUnary, processUnary, filtrationUnary, _horizonUnary, witnessUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _filtrationRow, _witnessRow,
    _routesRow, _probRow, _pkgOriginal⟩ := packet
  have prefixRouteUnary : UnaryHistory prefixRoute :=
    unary_cont_closed filtrationUnary prefixUnary prefixRow
  have eventReadUnary : UnaryHistory eventRead :=
    unary_cont_closed prefixRouteUnary witnessUnary eventReadRow
  exact
    ⟨probUnary, processUnary, filtrationUnary, witnessUnary, prefixUnary,
      prefixRouteUnary, eventReadUnary, prefixRow, eventReadRow, provenanceSig⟩

end BEDC.Derived.StoppingTimeUp
