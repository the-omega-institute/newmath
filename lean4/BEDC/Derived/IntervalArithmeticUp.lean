import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntervalArithmeticEndpointPacket [AskSetup] [PackageSetup]
    (lower upper lowerObs upperObs enclosure provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory lowerObs ∧
    UnaryHistory upperObs ∧ UnaryHistory provenance ∧ UnaryHistory enclosure ∧
      UnaryHistory endpoint ∧ Cont lower upper enclosure ∧
        Cont lowerObs upperObs endpoint ∧ PkgSig bundle endpoint pkg

theorem IntervalArithmeticEndpointPacket_classifier_transport [AskSetup] [PackageSetup]
    {lower upper lowerObs upperObs enclosure provenance endpoint lower' upper' lowerObs'
      upperObs' enclosure' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalArithmeticEndpointPacket lower upper lowerObs upperObs enclosure provenance
        endpoint bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          hsame lowerObs lowerObs' ->
            hsame upperObs upperObs' ->
              hsame provenance provenance' ->
                Cont lower' upper' enclosure' ->
                  Cont lowerObs' upperObs' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      IntervalArithmeticEndpointPacket lower' upper' lowerObs' upperObs'
                          enclosure' provenance' endpoint' bundle pkg ∧
                        hsame enclosure enclosure' ∧ hsame endpoint endpoint' := by
  intro packet sameLower sameUpper sameLowerObs sameUpperObs sameProvenance enclosureRow'
    endpointRow' endpointPkg'
  obtain ⟨lowerUnary, upperUnary, lowerObsUnary, upperObsUnary, provenanceUnary,
    _enclosureUnary, _endpointUnary, enclosureRow, endpointRow, _endpointPkg⟩ := packet
  have lowerUnary' : UnaryHistory lower' :=
    unary_transport lowerUnary sameLower
  have upperUnary' : UnaryHistory upper' :=
    unary_transport upperUnary sameUpper
  have lowerObsUnary' : UnaryHistory lowerObs' :=
    unary_transport lowerObsUnary sameLowerObs
  have upperObsUnary' : UnaryHistory upperObs' :=
    unary_transport upperObsUnary sameUpperObs
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have enclosureUnary' : UnaryHistory enclosure' :=
    unary_cont_closed lowerUnary' upperUnary' enclosureRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed lowerObsUnary' upperObsUnary' endpointRow'
  have sameEnclosure : hsame enclosure enclosure' :=
    cont_respects_hsame sameLower sameUpper enclosureRow enclosureRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLowerObs sameUpperObs endpointRow endpointRow'
  exact And.intro
    (And.intro lowerUnary'
      (And.intro upperUnary'
        (And.intro lowerObsUnary'
          (And.intro upperObsUnary'
            (And.intro provenanceUnary'
              (And.intro enclosureUnary'
                (And.intro endpointUnary'
                  (And.intro enclosureRow' (And.intro endpointRow' endpointPkg')))))))))
    (And.intro sameEnclosure sameEndpoint)

theorem IntervalArithmeticEndpointPacket_realup_enclosure_soundness [AskSetup] [PackageSetup]
    {lower upper lowerObs upperObs enclosure provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory lower ->
    UnaryHistory upper ->
    UnaryHistory lowerObs ->
    UnaryHistory upperObs ->
    Cont lower upper enclosure ->
    Cont lowerObs upperObs provenance ->
    Cont enclosure provenance endpoint ->
    PkgSig bundle endpoint pkg ->
      UnaryHistory enclosure ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        hsame enclosure (append lower upper) ∧ hsame provenance (append lowerObs upperObs) ∧
          hsame endpoint (append enclosure provenance) ∧ PkgSig bundle endpoint pkg := by
  intro lowerUnary upperUnary lowerObsUnary upperObsUnary enclosureRow provenanceRow endpointRow
    pkgSig
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed lowerUnary upperUnary enclosureRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed lowerObsUnary upperObsUnary provenanceRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed enclosureUnary provenanceUnary endpointRow
  exact And.intro enclosureUnary
    (And.intro provenanceUnary
      (And.intro endpointUnary
        (And.intro enclosureRow
          (And.intro provenanceRow
            (And.intro endpointRow pkgSig)))))

end BEDC.Derived.IntervalArithmeticUp
