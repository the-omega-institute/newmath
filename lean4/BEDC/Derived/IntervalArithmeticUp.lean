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

theorem IntervalArithmeticEndpointPacket_outward_rounded_addition [AskSetup] [PackageSetup]
    {lowerA upperA lowerObsA upperObsA enclosureA provenanceA endpointA lowerB upperB
      lowerObsB upperObsB enclosureB provenanceB endpointB lowerC upperC lowerObsC
      upperObsC enclosureC endpointC : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalArithmeticEndpointPacket lowerA upperA lowerObsA upperObsA enclosureA provenanceA
        endpointA bundle pkg ->
      IntervalArithmeticEndpointPacket lowerB upperB lowerObsB upperObsB enclosureB provenanceB
          endpointB bundle pkg ->
        Cont lowerA lowerB lowerC ->
          Cont upperA upperB upperC ->
            Cont lowerObsA lowerObsB lowerObsC ->
              Cont upperObsA upperObsB upperObsC ->
                Cont lowerC upperC enclosureC ->
                  Cont lowerObsC upperObsC endpointC ->
                    PkgSig bundle endpointC pkg ->
                      IntervalArithmeticEndpointPacket lowerC upperC lowerObsC upperObsC
                          enclosureC provenanceA endpointC bundle pkg ∧
                        Cont lowerA lowerB lowerC ∧ Cont upperA upperB upperC := by
  intro packetA packetB lowerRow upperRow lowerObsRow upperObsRow enclosureRow endpointRow
    endpointSig
  obtain ⟨lowerUnaryA, upperUnaryA, lowerObsUnaryA, upperObsUnaryA, provenanceUnaryA,
    _enclosureUnaryA, _endpointUnaryA, _enclosureRowA, _endpointRowA, _endpointSigA⟩ :=
    packetA
  obtain ⟨lowerUnaryB, upperUnaryB, lowerObsUnaryB, upperObsUnaryB, _provenanceUnaryB,
    _enclosureUnaryB, _endpointUnaryB, _enclosureRowB, _endpointRowB, _endpointSigB⟩ :=
    packetB
  have lowerUnaryC : UnaryHistory lowerC :=
    unary_cont_closed lowerUnaryA lowerUnaryB lowerRow
  have upperUnaryC : UnaryHistory upperC :=
    unary_cont_closed upperUnaryA upperUnaryB upperRow
  have lowerObsUnaryC : UnaryHistory lowerObsC :=
    unary_cont_closed lowerObsUnaryA lowerObsUnaryB lowerObsRow
  have upperObsUnaryC : UnaryHistory upperObsC :=
    unary_cont_closed upperObsUnaryA upperObsUnaryB upperObsRow
  have enclosureUnaryC : UnaryHistory enclosureC :=
    unary_cont_closed lowerUnaryC upperUnaryC enclosureRow
  have endpointUnaryC : UnaryHistory endpointC :=
    unary_cont_closed lowerObsUnaryC upperObsUnaryC endpointRow
  exact
    ⟨⟨lowerUnaryC, upperUnaryC, lowerObsUnaryC, upperObsUnaryC, provenanceUnaryA,
        enclosureUnaryC, endpointUnaryC, enclosureRow, endpointRow, endpointSig⟩,
      lowerRow, upperRow⟩

end BEDC.Derived.IntervalArithmeticUp
