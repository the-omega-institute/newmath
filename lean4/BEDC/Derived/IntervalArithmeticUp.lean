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

def IntervalArithmeticPacket [AskSetup] [PackageSetup]
    (lower upper lowerObs upperObs enclosure package : BHist) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory lowerObs ∧ UnaryHistory upperObs ∧
    UnaryHistory enclosure ∧ UnaryHistory package ∧
      ∃ bundle : ProbeBundle ProbeName, ∃ pkg : Pkg, PkgSig bundle package pkg

theorem IntervalArithmeticPacket_outward_rounded_addition [AskSetup] [PackageSetup]
    {lowerA upperA lowerObsA upperObsA enclosureA lowerB upperB lowerObsB upperObsB
      enclosureB lowerC upperC lowerObsC upperObsC enclosureC packageA packageB endpointC :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalArithmeticPacket lowerA upperA lowerObsA upperObsA enclosureA packageA ->
      IntervalArithmeticPacket lowerB upperB lowerObsB upperObsB enclosureB packageB ->
        Cont lowerA lowerB lowerC -> Cont upperA upperB upperC ->
          Cont lowerObsA lowerObsB lowerObsC -> Cont upperObsA upperObsB upperObsC ->
            Cont enclosureA enclosureB enclosureC -> Cont packageA packageB endpointC ->
              PkgSig bundle endpointC pkg ->
                IntervalArithmeticPacket lowerC upperC lowerObsC upperObsC enclosureC
                    endpointC ∧
                  hsame lowerC (append lowerA lowerB) ∧ hsame upperC (append upperA upperB) := by
  intro packetA packetB lowerRow upperRow lowerObsRow upperObsRow enclosureRow packageRow pkgRow
  have lowerCUnary : UnaryHistory lowerC :=
    unary_cont_closed packetA.left packetB.left lowerRow
  have upperCUnary : UnaryHistory upperC :=
    unary_cont_closed packetA.right.left packetB.right.left upperRow
  have lowerObsCUnary : UnaryHistory lowerObsC :=
    unary_cont_closed packetA.right.right.left packetB.right.right.left lowerObsRow
  have upperObsCUnary : UnaryHistory upperObsC :=
    unary_cont_closed packetA.right.right.right.left packetB.right.right.right.left upperObsRow
  have enclosureCUnary : UnaryHistory enclosureC :=
    unary_cont_closed packetA.right.right.right.right.left
      packetB.right.right.right.right.left enclosureRow
  have endpointCUnary : UnaryHistory endpointC :=
    unary_cont_closed packetA.right.right.right.right.right.left
      packetB.right.right.right.right.right.left packageRow
  exact And.intro
    (And.intro lowerCUnary
      (And.intro upperCUnary
        (And.intro lowerObsCUnary
          (And.intro upperObsCUnary
            (And.intro enclosureCUnary
              (And.intro endpointCUnary
                (Exists.intro bundle (Exists.intro pkg pkgRow))))))))
    (And.intro lowerRow upperRow)

end BEDC.Derived.IntervalArithmeticUp
