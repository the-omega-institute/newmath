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

def IntervalArithmeticEndpointPacket_transport_chain [AskSetup] [PackageSetup]
    (lower upper lowerObs upperObs enclosure provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory provenance ∧
    Cont lower upper lowerObs ∧ Cont upper lowerObs upperObs ∧
      Cont lowerObs upperObs enclosure ∧ Cont enclosure provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem IntervalArithmeticEndpointPacket_transport [AskSetup] [PackageSetup]
    {lower upper lowerObs upperObs enclosure provenance endpoint lower' upper' lowerObs'
      upperObs' enclosure' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalArithmeticEndpointPacket_transport_chain lower upper lowerObs upperObs enclosure
        provenance endpoint bundle pkg ->
      hsame lower lower' -> hsame upper upper' -> hsame provenance provenance' ->
        Cont lower' upper' lowerObs' -> Cont upper' lowerObs' upperObs' ->
          Cont lowerObs' upperObs' enclosure' -> Cont enclosure' provenance' endpoint' ->
            PkgSig bundle endpoint' pkg ->
              IntervalArithmeticEndpointPacket_transport_chain lower' upper' lowerObs'
                  upperObs' enclosure' provenance' endpoint' bundle pkg ∧
                hsame lowerObs lowerObs' ∧ hsame upperObs upperObs' ∧
                  hsame enclosure enclosure' ∧ hsame endpoint endpoint' := by
  intro packet sameLower sameUpper sameProvenance
  intro lowerRow' upperRow' enclosureRow' endpointRow' pkgSig'
  have sameLowerObs : hsame lowerObs lowerObs' :=
    cont_respects_hsame sameLower sameUpper
      packet.right.right.right.left lowerRow'
  have sameUpperObs : hsame upperObs upperObs' :=
    cont_respects_hsame sameUpper sameLowerObs
      packet.right.right.right.right.left upperRow'
  have sameEnclosure : hsame enclosure enclosure' :=
    cont_respects_hsame sameLowerObs sameUpperObs
      packet.right.right.right.right.right.left enclosureRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameEnclosure sameProvenance
      packet.right.right.right.right.right.right.left endpointRow'
  have transported :
      IntervalArithmeticEndpointPacket_transport_chain lower' upper' lowerObs' upperObs'
          enclosure' provenance' endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameLower,
      unary_transport packet.right.left sameUpper,
      unary_transport packet.right.right.left sameProvenance,
      lowerRow',
      upperRow',
      enclosureRow',
      endpointRow',
      pkgSig'⟩
  exact ⟨transported, sameLowerObs, sameUpperObs, sameEnclosure, sameEndpoint⟩

end BEDC.Derived.IntervalArithmeticUp
