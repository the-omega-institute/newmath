import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealPacket [AskSetup] [PackageSetup]
    (schedule regseq endpoint modulus located apartness sealRow transportRow routeRow
      provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory regseq ∧ UnaryHistory endpoint ∧
    UnaryHistory modulus ∧ UnaryHistory located ∧ UnaryHistory apartness ∧
      UnaryHistory sealRow ∧ UnaryHistory transportRow ∧ UnaryHistory routeRow ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont schedule regseq endpoint ∧
          Cont endpoint modulus located ∧ Cont located apartness sealRow ∧
            PkgSig bundle provenance pkg

theorem BishopRealPacket_located_apartness_transport [AskSetup] [PackageSetup]
    {schedule regseq endpoint modulus located apartness sealRow transportRow routeRow provenance
      nameCert schedule' regseq' endpoint' modulus' located' apartness' sealRow'
      transportRow' routeRow' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealPacket schedule regseq endpoint modulus located apartness sealRow transportRow routeRow
        provenance nameCert bundle pkg ->
      hsame schedule schedule' ->
        hsame regseq regseq' ->
          hsame endpoint endpoint' ->
            hsame modulus modulus' ->
              hsame located located' ->
                hsame apartness apartness' ->
                  hsame sealRow sealRow' ->
                    hsame transportRow transportRow' ->
                      hsame routeRow routeRow' ->
                        hsame provenance provenance' ->
                          hsame nameCert nameCert' ->
                            Cont schedule' regseq' endpoint' ->
                              Cont endpoint' modulus' located' ->
                                Cont located' apartness' sealRow' ->
                                  PkgSig bundle provenance' pkg ->
                                    BishopRealPacket schedule' regseq' endpoint' modulus'
                                        located' apartness' sealRow' transportRow' routeRow'
                                        provenance' nameCert' bundle pkg ∧
                                      hsame sealRow sealRow' ∧ hsame located located' ∧
                                        hsame apartness apartness' := by
  intro packet sameSchedule sameRegseq sameEndpoint sameModulus sameLocated
  intro sameApartness sameSeal sameTransport sameRoute sameProvenance sameNameCert
  intro scheduleRegseqEndpoint endpointModulusLocated locatedApartnessSeal provenancePkg
  rcases packet with
    ⟨scheduleUnary, regseqUnary, endpointUnary, modulusUnary, locatedUnary,
      apartnessUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameCertUnary,
      _scheduleRegseqEndpoint, _endpointModulusLocated, _locatedApartnessSeal,
      _provenancePkg⟩
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have regseqUnary' : UnaryHistory regseq' :=
    unary_transport regseqUnary sameRegseq
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have locatedUnary' : UnaryHistory located' :=
    unary_transport locatedUnary sameLocated
  have apartnessUnary' : UnaryHistory apartness' :=
    unary_transport apartnessUnary sameApartness
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have transportUnary' : UnaryHistory transportRow' :=
    unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory routeRow' :=
    unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  exact
    ⟨⟨scheduleUnary', regseqUnary', endpointUnary', modulusUnary', locatedUnary',
        apartnessUnary', sealUnary', transportUnary', routeUnary', provenanceUnary',
        nameCertUnary', scheduleRegseqEndpoint, endpointModulusLocated,
        locatedApartnessSeal, provenancePkg⟩,
      sameSeal, sameLocated, sameApartness⟩

end BEDC.Derived.BishopRealUp
