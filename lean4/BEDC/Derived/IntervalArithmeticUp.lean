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

theorem IntervalArithmeticEndpointPacket_outward_addition_closure [AskSetup] [PackageSetup]
    {lowerA upperA lowerObsA upperObsA enclosureA provenanceA endpointA lowerB upperB
      lowerC upperC package : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalArithmeticEndpointPacket lowerA upperA lowerObsA upperObsA enclosureA
        provenanceA endpointA bundle pkg ->
      UnaryHistory lowerB ->
        UnaryHistory upperB ->
          Cont lowerA lowerB lowerC ->
            Cont upperA upperB upperC ->
              Cont lowerC upperC package ->
                PkgSig bundle endpointA pkg ->
                  UnaryHistory lowerC ∧ UnaryHistory upperC ∧ UnaryHistory package := by
  intro packet lowerBUnary upperBUnary lowerRow upperRow packageRow _
  have lowerCUnary : UnaryHistory lowerC :=
    unary_cont_closed packet.left lowerBUnary lowerRow
  have upperCUnary : UnaryHistory upperC :=
    unary_cont_closed packet.right.left upperBUnary upperRow
  have packageUnary : UnaryHistory package :=
    unary_cont_closed lowerCUnary upperCUnary packageRow
  exact ⟨lowerCUnary, upperCUnary, packageUnary⟩

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
            Cont lowerC provenanceA lowerObsC ->
              Cont upperC provenanceA upperObsC ->
                Cont lowerObsC upperObsC enclosureC ->
                  Cont enclosureC provenanceA endpointC ->
                    PkgSig bundle endpointC pkg ->
                      IntervalArithmeticEndpointPacket lowerC upperC lowerObsC upperObsC
                          enclosureC provenanceA endpointC bundle pkg ∧
                        Cont lowerA lowerB lowerC ∧ Cont upperA upperB upperC := by
  intro packetA packetB lowerRow upperRow lowerObsRow upperObsRow enclosureRow endpointRow
    endpointSig
  obtain ⟨lowerUnaryA, upperUnaryA, provenanceUnaryA, _lowerObsRowA, _upperObsRowA,
    _enclosureRowA, _endpointRowA, _endpointSigA⟩ :=
    packetA
  obtain ⟨lowerUnaryB, upperUnaryB, _provenanceUnaryB, _lowerObsRowB, _upperObsRowB,
    _enclosureRowB, _endpointRowB, _endpointSigB⟩ :=
    packetB
  have lowerUnaryC : UnaryHistory lowerC :=
    unary_cont_closed lowerUnaryA lowerUnaryB lowerRow
  have upperUnaryC : UnaryHistory upperC :=
    unary_cont_closed upperUnaryA upperUnaryB upperRow
  have lowerObsUnaryC : UnaryHistory lowerObsC :=
    unary_cont_closed lowerUnaryC provenanceUnaryA lowerObsRow
  have upperObsUnaryC : UnaryHistory upperObsC :=
    unary_cont_closed upperUnaryC provenanceUnaryA upperObsRow
  have enclosureUnaryC : UnaryHistory enclosureC :=
    unary_cont_closed lowerObsUnaryC upperObsUnaryC enclosureRow
  have endpointUnaryC : UnaryHistory endpointC :=
    unary_cont_closed enclosureUnaryC provenanceUnaryA endpointRow
  exact
    ⟨⟨lowerUnaryC, upperUnaryC, provenanceUnaryA, lowerObsRow, upperObsRow, enclosureRow,
        endpointRow, endpointSig⟩,
      lowerRow, upperRow⟩

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
