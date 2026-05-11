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
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory provenance ∧
    Cont lower provenance lowerObs ∧ Cont upper provenance upperObs ∧
      Cont lowerObs upperObs enclosure ∧ Cont enclosure provenance endpoint ∧
        PkgSig bundle endpoint pkg

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
                Cont lower' provenance' lowerObs' ->
                  Cont upper' provenance' upperObs' ->
                    Cont lowerObs' upperObs' enclosure' ->
                      Cont enclosure' provenance' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          IntervalArithmeticEndpointPacket lower' upper' lowerObs' upperObs'
                              enclosure' provenance' endpoint' bundle pkg ∧
                            hsame enclosure enclosure' ∧ hsame endpoint endpoint' := by
  intro packet sameLower sameUpper sameLowerObs sameUpperObs sameProvenance lowerObsRow'
    upperObsRow' enclosureRow' endpointRow' endpointPkg'
  obtain ⟨lowerUnary, upperUnary, provenanceUnary, lowerObsRow, upperObsRow, enclosureRow,
    endpointRow, _endpointPkg⟩ := packet
  have lowerUnary' : UnaryHistory lower' :=
    unary_transport lowerUnary sameLower
  have upperUnary' : UnaryHistory upper' :=
    unary_transport upperUnary sameUpper
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have lowerObsUnary' : UnaryHistory lowerObs' :=
    unary_cont_closed lowerUnary' provenanceUnary' lowerObsRow'
  have upperObsUnary' : UnaryHistory upperObs' :=
    unary_cont_closed upperUnary' provenanceUnary' upperObsRow'
  have enclosureUnary' : UnaryHistory enclosure' :=
    unary_cont_closed lowerObsUnary' upperObsUnary' enclosureRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed enclosureUnary' provenanceUnary' endpointRow'
  have sameEnclosure : hsame enclosure enclosure' :=
    cont_respects_hsame sameLowerObs sameUpperObs enclosureRow enclosureRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameEnclosure sameProvenance endpointRow endpointRow'
  exact And.intro
    (And.intro lowerUnary'
      (And.intro upperUnary'
        (And.intro provenanceUnary'
          (And.intro lowerObsRow'
            (And.intro upperObsRow'
              (And.intro enclosureRow'
                (And.intro endpointRow' endpointPkg')))))))
    (And.intro sameEnclosure sameEndpoint)

theorem IntervalArithmeticEndpointPacket_public_certificate_surface [AskSetup] [PackageSetup]
    {lower upper lowerObs upperObs enclosure provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalArithmeticEndpointPacket lower upper lowerObs upperObs enclosure provenance endpoint
        bundle pkg ->
      UnaryHistory lowerObs ∧ UnaryHistory upperObs ∧ UnaryHistory enclosure ∧
        hsame enclosure (append lowerObs upperObs) ∧ UnaryHistory endpoint ∧
          hsame endpoint (append enclosure provenance) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have lowerUnary : UnaryHistory lower :=
    packet.left
  have upperUnary : UnaryHistory upper :=
    packet.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.left
  have lowerObsRow : Cont lower provenance lowerObs :=
    packet.right.right.right.left
  have upperObsRow : Cont upper provenance upperObs :=
    packet.right.right.right.right.left
  have enclosureRow : Cont lowerObs upperObs enclosure :=
    packet.right.right.right.right.right.left
  have endpointRow : Cont enclosure provenance endpoint :=
    packet.right.right.right.right.right.right.left
  have packageBoundary : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right
  have lowerObsUnary : UnaryHistory lowerObs :=
    unary_cont_closed lowerUnary provenanceUnary lowerObsRow
  have upperObsUnary : UnaryHistory upperObs :=
    unary_cont_closed upperUnary provenanceUnary upperObsRow
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed lowerObsUnary upperObsUnary enclosureRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed enclosureUnary provenanceUnary endpointRow
  exact And.intro lowerObsUnary
    (And.intro upperObsUnary
      (And.intro enclosureUnary
        (And.intro enclosureRow
          (And.intro endpointUnary
            (And.intro endpointRow packageBoundary)))))

end BEDC.Derived.IntervalArithmeticUp
