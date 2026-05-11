import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegSeqRatStreamCarrier [AskSetup] [PackageSetup]
    (schedule index endpoint radius regularity transport provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory index ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    Cont index endpoint regularity ∧ Cont regularity radius transport ∧
      Cont transport schedule provenance ∧ PkgSig bundle provenance pkg

theorem RegSeqRatStreamCarrier_regularity_obligation_surface [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity transport provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity transport provenance
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity transport e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity transport e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity transport e
                bundle pkg ∧ hsame row e)
          hsame ∧ Cont index endpoint regularity ∧ Cont regularity radius transport ∧
            Cont transport schedule provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier
  rcases carrier with
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, indexEndpointRegularity,
      regularityRadiusTransport, transportScheduleProvenance, pkgSig⟩
  have carrierPacket :
      RegSeqRatStreamCarrier schedule index endpoint radius regularity transport provenance
          bundle pkg :=
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, indexEndpointRegularity,
      regularityRadiusTransport, transportScheduleProvenance, pkgSig⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity transport e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity transport e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity transport e
                bundle pkg ∧ hsame row e)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro provenance
            (Exists.intro provenance (And.intro carrierPacket (hsame_refl provenance)))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          cases source with
          | intro e data =>
              cases data with
              | intro packetE sameRowE =>
                  exact Exists.intro e
                    (And.intro packetE (hsame_trans (hsame_symm same) sameRowE))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨cert, indexEndpointRegularity, regularityRadiusTransport, transportScheduleProvenance,
    pkgSig⟩

theorem RegSeqRatStreamCarrier_classifier_transport [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity transport provenance schedule' endpoint'
      radius' regularity' transport' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity transport provenance
        bundle pkg ->
      hsame schedule schedule' ->
        hsame endpoint endpoint' ->
          hsame radius radius' ->
            Cont index endpoint' regularity' ->
              Cont regularity' radius' transport' ->
                Cont transport' schedule' provenance' ->
                  PkgSig bundle provenance' pkg ->
                    RegSeqRatStreamCarrier schedule' index endpoint' radius' regularity'
                        transport' provenance' bundle pkg ∧
                      hsame regularity regularity' ∧ hsame transport transport' ∧
                        hsame provenance provenance' := by
  intro carrier sameSchedule sameEndpoint sameRadius indexEndpointRegularity'
    regularityRadiusTransport' transportScheduleProvenance' pkgSig'
  rcases carrier with
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, indexEndpointRegularity,
      regularityRadiusTransport, transportScheduleProvenance, _pkgSig⟩
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have sameRegularity : hsame regularity regularity' :=
    cont_respects_hsame (hsame_refl index) sameEndpoint indexEndpointRegularity
      indexEndpointRegularity'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameRegularity sameRadius regularityRadiusTransport
      regularityRadiusTransport'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameSchedule transportScheduleProvenance
      transportScheduleProvenance'
  have carrier' :
      RegSeqRatStreamCarrier schedule' index endpoint' radius' regularity' transport'
          provenance' bundle pkg :=
    ⟨scheduleUnary', indexUnary, endpointUnary', radiusUnary', indexEndpointRegularity',
      regularityRadiusTransport', transportScheduleProvenance', pkgSig'⟩
  exact ⟨carrier', sameRegularity, sameTransport, sameProvenance⟩

end BEDC.Derived.RegSeqRatUp
