import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def CauchyModulusLedgerPacket
    (precision threshold tolerance observation consumption provenance window : BHist) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ RatHistoryCarrier tolerance ∧
    Cont precision threshold window ∧ Cont window tolerance consumption ∧
      Cont consumption observation provenance

theorem CauchyModulusLedgerPacket_hsame_stability
    {precision precision' threshold threshold' tolerance tolerance' observation observation'
      consumption provenance window : BHist} :
    CauchyModulusLedgerPacket precision threshold tolerance observation consumption provenance window ->
      hsame precision' precision -> hsame threshold' threshold -> hsame tolerance' tolerance ->
        hsame observation' observation ->
          exists consumption' provenance' window' : BHist,
            CauchyModulusLedgerPacket precision' threshold' tolerance' observation'
              consumption' provenance' window' ∧
              hsame window window' ∧ hsame consumption consumption' ∧
                hsame provenance provenance' := by
  intro packet samePrecision sameThreshold sameTolerance sameObservation
  cases packet with
  | intro precisionUnary packetRest =>
      cases packetRest with
      | intro thresholdUnary packetRest =>
          cases packetRest with
          | intro toleranceCarrier packetRest =>
              cases packetRest with
              | intro windowRow packetRest =>
                  cases packetRest with
                  | intro consumptionRow provenanceRow =>
                      let window' := append precision' threshold'
                      let consumption' := append window' tolerance'
                      let provenance' := append consumption' observation'
                      have precisionUnary' : UnaryHistory precision' :=
                        unary_transport_symm precisionUnary samePrecision
                      have thresholdUnary' : UnaryHistory threshold' :=
                        unary_transport_symm thresholdUnary sameThreshold
                      have toleranceCarrier' : RatHistoryCarrier tolerance' :=
                        RatHistoryCarrier_hsame_transport (hsame_symm sameTolerance)
                          toleranceCarrier
                      have windowRow' : Cont precision' threshold' window' := by
                        rfl
                      have consumptionRow' : Cont window' tolerance' consumption' := by
                        rfl
                      have provenanceRow' : Cont consumption' observation' provenance' := by
                        rfl
                      have sameWindow : hsame window window' :=
                        cont_respects_hsame (hsame_symm samePrecision)
                          (hsame_symm sameThreshold) windowRow windowRow'
                      have sameConsumption : hsame consumption consumption' :=
                        cont_respects_hsame sameWindow (hsame_symm sameTolerance)
                          consumptionRow consumptionRow'
                      have sameProvenance : hsame provenance provenance' :=
                        cont_respects_hsame sameConsumption (hsame_symm sameObservation)
                          provenanceRow provenanceRow'
                      exact ⟨consumption', provenance', window',
                        ⟨precisionUnary', thresholdUnary', toleranceCarrier', windowRow',
                          consumptionRow', provenanceRow'⟩,
                        sameWindow, sameConsumption, sameProvenance⟩

def CauchyModulusCarrier [AskSetup] [PackageSetup]
    (precision threshold tolerance schedule consumption provenance window : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory tolerance ∧
    UnaryHistory schedule ∧ UnaryHistory consumption ∧ UnaryHistory provenance ∧
      UnaryHistory window ∧ Cont precision threshold consumption ∧
        Cont tolerance schedule provenance ∧ Cont consumption provenance window ∧
          PkgSig bundle window pkg

def CauchyModulusClassifier [AskSetup] [PackageSetup]
    (precision threshold tolerance schedule consumption provenance window precision' threshold'
      tolerance' schedule' consumption' provenance' window' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CauchyModulusCarrier precision threshold tolerance schedule consumption provenance window
      bundle pkg ∧
    CauchyModulusCarrier precision' threshold' tolerance' schedule' consumption' provenance'
        window' bundle pkg ∧
      hsame precision precision' ∧ hsame threshold threshold' ∧ hsame tolerance tolerance' ∧
        hsame schedule schedule' ∧ hsame consumption consumption' ∧
          hsame provenance provenance' ∧ hsame window window'

theorem CauchyModulusCarrier_hsame_stability [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule consumption provenance window precision' threshold'
      tolerance' schedule' consumption' provenance' window' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusCarrier precision threshold tolerance schedule consumption provenance window
        bundle pkg ->
      hsame precision precision' ->
        hsame threshold threshold' ->
          hsame tolerance tolerance' ->
            hsame schedule schedule' ->
              Cont precision' threshold' consumption' ->
                Cont tolerance' schedule' provenance' ->
                  Cont consumption' provenance' window' ->
                    PkgSig bundle window' pkg ->
                      CauchyModulusCarrier precision' threshold' tolerance' schedule'
                          consumption' provenance' window' bundle pkg ∧
                        hsame consumption consumption' ∧ hsame provenance provenance' ∧
                          hsame window window' := by
  intro carrier samePrecision sameThreshold sameTolerance sameSchedule consumptionRow'
    provenanceRow' windowRow' pkgSig'
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport carrier.left samePrecision
  have thresholdUnary' : UnaryHistory threshold' :=
    unary_transport carrier.right.left sameThreshold
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport carrier.right.right.left sameTolerance
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport carrier.right.right.right.left sameSchedule
  have consumptionUnary' : UnaryHistory consumption' :=
    unary_cont_closed precisionUnary' thresholdUnary' consumptionRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed toleranceUnary' scheduleUnary' provenanceRow'
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed consumptionUnary' provenanceUnary' windowRow'
  have sameConsumption : hsame consumption consumption' :=
    cont_respects_hsame samePrecision sameThreshold
      carrier.right.right.right.right.right.right.right.left consumptionRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTolerance sameSchedule
      carrier.right.right.right.right.right.right.right.right.left provenanceRow'
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameConsumption sameProvenance
      carrier.right.right.right.right.right.right.right.right.right.left windowRow'
  constructor
  · exact
      And.intro precisionUnary'
        (And.intro thresholdUnary'
          (And.intro toleranceUnary'
            (And.intro scheduleUnary'
              (And.intro consumptionUnary'
                (And.intro provenanceUnary'
                  (And.intro windowUnary'
                    (And.intro consumptionRow'
                      (And.intro provenanceRow'
                        (And.intro windowRow' pkgSig')))))))))
  · exact And.intro sameConsumption (And.intro sameProvenance sameWindow)

def CauchyModulusPacket [AskSetup] [PackageSetup]
    (precision threshold tolerance schedule observationLedger consumptionLedger window
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory tolerance ∧
    UnaryHistory schedule ∧ UnaryHistory observationLedger ∧
      UnaryHistory consumptionLedger ∧ UnaryHistory window ∧ UnaryHistory endpoint ∧
        Cont precision threshold schedule ∧ Cont schedule tolerance observationLedger ∧
          Cont observationLedger consumptionLedger window ∧ Cont window threshold endpoint ∧
            PkgSig bundle endpoint pkg

theorem CauchyModulusPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule observationLedger consumptionLedger window endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusPacket precision threshold tolerance schedule observationLedger
      consumptionLedger window endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              CauchyModulusPacket precision threshold tolerance schedule observationLedger
                consumptionLedger window e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              CauchyModulusPacket precision threshold tolerance schedule observationLedger
                consumptionLedger window e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              CauchyModulusPacket precision threshold tolerance schedule observationLedger
                consumptionLedger window e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont precision threshold schedule ∧ Cont schedule tolerance observationLedger ∧
          Cont observationLedger consumptionLedger window ∧ Cont window threshold endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpoint (Exists.intro endpoint (And.intro packet (hsame_refl endpoint)))
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
              exact Exists.intro e
                (And.intro data.left (hsame_trans (hsame_symm same) data.right))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · exact
      And.intro packet.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right.right.right.right.right.right)))

theorem CauchyModulusPacket_cont_window_closure [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule observationLedger consumptionLedger window
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusPacket precision threshold tolerance schedule observationLedger
        consumptionLedger window endpoint bundle pkg ->
      UnaryHistory threshold ∧ UnaryHistory tolerance ∧ UnaryHistory observationLedger ∧
        UnaryHistory consumptionLedger ∧ Cont precision threshold schedule ∧
          Cont schedule tolerance observationLedger ∧
            Cont observationLedger consumptionLedger window ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.right.left
    (And.intro packet.right.right.left
      (And.intro packet.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
                packet.right.right.right.right.right.right.right.right.right.right.right.right))))))

def CauchyModulusCarrierPacket
    (precision threshold tolerance observationA observationB ledger provenance : BHist) : Prop :=
  UnaryHistory precision ∧
    UnaryHistory threshold ∧
      PositiveUnaryDenominator tolerance ∧
        UnaryHistory observationA ∧
          UnaryHistory observationB ∧
            UnaryHistory ledger ∧
              UnaryHistory provenance ∧
                Cont precision tolerance threshold ∧
                  Cont threshold observationA ledger ∧
                    Cont ledger provenance observationB

def CauchyModulusClassifierPacket
    (precision threshold tolerance observationA observationB ledger provenance
      precision' threshold' tolerance' observationA' observationB' ledger'
      provenance' : BHist) : Prop :=
  CauchyModulusCarrierPacket precision threshold tolerance observationA observationB ledger
      provenance ∧
    CauchyModulusCarrierPacket precision' threshold' tolerance' observationA' observationB'
        ledger' provenance' ∧
      hsame precision precision' ∧
        hsame threshold threshold' ∧
          hsame tolerance tolerance' ∧
            hsame observationA observationA' ∧
              hsame observationB observationB' ∧
                hsame ledger ledger' ∧
                  hsame provenance provenance'

theorem CauchyModulusPacket_hsame_stability
    {precision threshold tolerance observationA observationB ledger provenance
      precision' threshold' tolerance' observationA' observationB' ledger'
      provenance' : BHist}
    (packet :
      CauchyModulusCarrierPacket precision threshold tolerance observationA observationB ledger
        provenance)
    (samePrecision : hsame precision precision')
    (sameThreshold : hsame threshold threshold')
    (sameTolerance : hsame tolerance tolerance')
    (sameObservationA : hsame observationA observationA')
    (sameObservationB : hsame observationB observationB')
    (sameLedger : hsame ledger ledger')
    (sameProvenance : hsame provenance provenance') :
    CauchyModulusCarrierPacket precision' threshold' tolerance' observationA' observationB'
        ledger' provenance' ∧
      CauchyModulusClassifierPacket precision threshold tolerance observationA observationB ledger
        provenance precision' threshold' tolerance' observationA' observationB' ledger'
        provenance' ∧
        Cont precision' tolerance' threshold' ∧
          Cont threshold' observationA' ledger' ∧
            Cont ledger' provenance' observationB' := by
  have precisionUnary : UnaryHistory precision' :=
    unary_transport packet.left samePrecision
  have thresholdUnary : UnaryHistory threshold' :=
    unary_transport packet.right.left sameThreshold
  have tolerancePositive : PositiveUnaryDenominator tolerance' :=
    PositiveUnaryDenominator_hsame_transport sameTolerance packet.right.right.left
  have observationAUnary : UnaryHistory observationA' :=
    unary_transport packet.right.right.right.left sameObservationA
  have observationBUnary : UnaryHistory observationB' :=
    unary_transport packet.right.right.right.right.left sameObservationB
  have ledgerUnary : UnaryHistory ledger' :=
    unary_transport packet.right.right.right.right.right.left sameLedger
  have provenanceUnary : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have thresholdRoute : Cont precision' tolerance' threshold' :=
    cont_hsame_transport samePrecision sameTolerance sameThreshold
      packet.right.right.right.right.right.right.right.left
  have ledgerRoute : Cont threshold' observationA' ledger' :=
    cont_hsame_transport sameThreshold sameObservationA sameLedger
      packet.right.right.right.right.right.right.right.right.left
  have observationRoute : Cont ledger' provenance' observationB' :=
    cont_hsame_transport sameLedger sameProvenance sameObservationB
      packet.right.right.right.right.right.right.right.right.right
  have targetPacket :
      CauchyModulusCarrierPacket precision' threshold' tolerance' observationA'
        observationB' ledger' provenance' :=
    And.intro precisionUnary
      (And.intro thresholdUnary
        (And.intro tolerancePositive
          (And.intro observationAUnary
            (And.intro observationBUnary
              (And.intro ledgerUnary
                (And.intro provenanceUnary
                  (And.intro thresholdRoute
                    (And.intro ledgerRoute observationRoute))))))))
  have classified :
      CauchyModulusClassifierPacket precision threshold tolerance observationA observationB ledger
        provenance precision' threshold' tolerance' observationA' observationB' ledger'
        provenance' :=
    And.intro packet
      (And.intro targetPacket
        (And.intro samePrecision
          (And.intro sameThreshold
            (And.intro sameTolerance
              (And.intro sameObservationA
                (And.intro sameObservationB
                  (And.intro sameLedger sameProvenance)))))))
  exact And.intro targetPacket
    (And.intro classified (And.intro thresholdRoute (And.intro ledgerRoute observationRoute)))

theorem CauchyModulusPacket_regseqrat_regularity_handoff
    {precision threshold tolerance observationA observationB ledger provenance : BHist}
    (packet :
      CauchyModulusCarrierPacket precision threshold tolerance observationA observationB ledger
        provenance) :
    exists representative regularity : BHist,
      Cont observationA observationB representative ∧
        Cont representative ledger regularity ∧
          UnaryHistory representative ∧
            UnaryHistory regularity ∧
              PositiveUnaryDenominator tolerance ∧
                hsame regularity (append representative ledger) := by
  let representative := append observationA observationB
  let regularity := append representative ledger
  have representativeRow : Cont observationA observationB representative := by
    rfl
  have regularityRow : Cont representative ledger regularity := by
    rfl
  have representativeUnary : UnaryHistory representative :=
    unary_cont_closed packet.right.right.right.left packet.right.right.right.right.left
      representativeRow
  have regularityUnary : UnaryHistory regularity :=
    unary_cont_closed representativeUnary packet.right.right.right.right.right.left
      regularityRow
  exact ⟨representative, regularity, representativeRow, regularityRow, representativeUnary,
    regularityUnary, packet.right.right.left, regularityRow⟩

theorem CauchyModulusCarrier_finite_cont_window_closure
    {precision threshold tolerance observationA observationB ledger provenance window : BHist} :
    CauchyModulusCarrierPacket precision threshold tolerance observationA observationB ledger
        provenance ->
      Cont precision threshold window ->
        UnaryHistory window ∧
          Cont precision threshold window ∧
            Cont threshold observationA ledger ∧
              Cont ledger provenance observationB ∧ PositiveUnaryDenominator tolerance := by
  intro packet windowRow
  have windowUnary : UnaryHistory window :=
    unary_cont_closed packet.left packet.right.left windowRow
  exact And.intro windowUnary
    (And.intro windowRow
      (And.intro packet.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right
          packet.right.right.left)))

def CauchyModulusTailWindow
    (packet precision threshold tolerance schedule ledger pkg : BHist) : Prop :=
  UnaryHistory precision ∧
    UnaryHistory threshold ∧
      PositiveUnaryDenominator tolerance ∧
        Cont threshold tolerance schedule ∧ Cont schedule ledger packet ∧ hsame pkg packet

theorem CauchyModulusTailWindow_smaller_tolerance_transport
    {packet precision threshold tolerance schedule ledger pkg tolerance2 : BHist} :
    CauchyModulusTailWindow packet precision threshold tolerance schedule ledger pkg ->
      PositiveUnaryDenominator tolerance2 -> hsame tolerance tolerance2 ->
        exists schedule2 : BHist, exists packet2 : BHist,
          CauchyModulusTailWindow packet2 precision threshold tolerance2 schedule2 ledger pkg /\
            hsame schedule schedule2 /\ Cont schedule2 ledger packet2 := by
  intro window tolerance2Positive sameTolerance
  have transportedSchedule : Cont threshold tolerance2 schedule :=
    cont_hsame_transport (hsame_refl threshold) sameTolerance (hsame_refl schedule)
      window.right.right.right.left
  exact Exists.intro schedule
    (Exists.intro packet
      (And.intro
        (And.intro window.left
          (And.intro window.right.left
            (And.intro tolerance2Positive
              (And.intro transportedSchedule
                (And.intro window.right.right.right.right.left
                  window.right.right.right.right.right)))))
        (And.intro (hsame_refl schedule) window.right.right.right.right.left)))

theorem CauchyModulus_monotone_tail_refinement_window
    {tol refined threshold oldLedger refinedLedger tail : BHist} :
    RatHistoryCarrier tol -> UnaryHistory tail -> Cont tol tail refined ->
      Cont threshold tol oldLedger -> Cont threshold refined refinedLedger ->
        RatHistoryCarrier refined ∧ hsame refined (append tol tail) ∧
          hsame oldLedger (append threshold tol) ∧
            hsame refinedLedger (append threshold refined) := by
  intro tolCarrier tailUnary refineCont oldLedgerCont refinedLedgerCont
  have refinedCarrier : RatHistoryCarrier refined := by
    cases refineCont
    exact RatHistoryCarrier_append_unary_denominator_closed tolCarrier tailUnary
  exact And.intro refinedCarrier
    (And.intro refineCont
      (And.intro oldLedgerCont refinedLedgerCont))

theorem CauchyModulusLedgerPacket_regseqrat_regularity_rows
    {precision threshold tolerance observation observation' consumption provenance provenance'
      window : BHist} :
    CauchyModulusLedgerPacket precision threshold tolerance observation consumption provenance
        window ->
      hsame observation observation' -> Cont consumption observation' provenance' ->
        RatHistoryCarrier tolerance ∧ UnaryHistory window ∧ Cont window tolerance consumption ∧
          hsame provenance provenance' := by
  intro packet sameObservation provenanceRow'
  have toleranceCarrier : RatHistoryCarrier tolerance := packet.right.right.left
  have precisionUnary : UnaryHistory precision := packet.left
  have thresholdUnary : UnaryHistory threshold := packet.right.left
  have windowRow : Cont precision threshold window := packet.right.right.right.left
  have consumptionRow : Cont window tolerance consumption := packet.right.right.right.right.left
  have provenanceRow : Cont consumption observation provenance :=
    packet.right.right.right.right.right
  have windowUnary : UnaryHistory window :=
    unary_cont_closed precisionUnary thresholdUnary windowRow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame (hsame_refl consumption) sameObservation provenanceRow provenanceRow'
  exact And.intro toleranceCarrier
    (And.intro windowUnary (And.intro consumptionRow sameProvenance))

end BEDC.Derived.CauchyModulusUp
