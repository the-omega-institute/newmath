import BEDC.Derived.RatUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicRatCorePackageCarrier [AskSetup] [PackageSetup]
    (mantissa exponent ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  RatHistoryCarrier mantissa ∧
    UnaryHistory exponent ∧
      UnaryHistory ledger ∧
        Cont exponent ledger provenance ∧
          Cont provenance mantissa endpoint ∧
            PkgSig bundle endpoint pkg

theorem DyadicRatCoreCarrier_denominator_ledger_transport [AskSetup] [PackageSetup]
    {mantissa exponent ledger provenance endpoint mantissa' exponent' ledger' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRatCorePackageCarrier mantissa exponent ledger provenance endpoint bundle pkg ->
      hsame mantissa mantissa' ->
        hsame exponent exponent' ->
          hsame ledger ledger' ->
            Cont exponent' ledger' provenance' ->
              Cont provenance' mantissa' endpoint' ->
                PkgSig bundle endpoint' pkg ->
                  DyadicRatCorePackageCarrier mantissa' exponent' ledger' provenance' endpoint'
                      bundle pkg ∧
                    UnaryHistory exponent' ∧
                      hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameMantissa sameExponent sameLedger provenanceRow' endpointRow' pkgSig'
  have mantissaCarrier' : RatHistoryCarrier mantissa' :=
    RatHistoryCarrier_hsame_transport sameMantissa carrier.left
  have exponentUnary' : UnaryHistory exponent' :=
    unary_transport carrier.right.left sameExponent
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport carrier.right.right.left sameLedger
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameExponent sameLedger carrier.right.right.right.left provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameMantissa carrier.right.right.right.right.left
      endpointRow'
  exact And.intro
    (And.intro mantissaCarrier'
      (And.intro exponentUnary'
        (And.intro ledgerUnary'
          (And.intro provenanceRow'
            (And.intro endpointRow' pkgSig')))))
        (And.intro exponentUnary' (And.intro sameProvenance sameEndpoint))

def DyadicRatCorePacket
    (_mantissa exponent ledger provenance denominator window packet : BHist) : Prop :=
  UnaryHistory exponent ∧ Cont exponent ledger denominator ∧
    Cont denominator provenance window ∧ hsame packet window

theorem DyadicRatCorePacket_denominator_ledger_transport
    {mantissa mantissa' exponent exponent' ledger ledger' provenance provenance' denominator
      denominator' window window' packet packet' : BHist}
    (hD : DyadicRatCorePacket mantissa exponent ledger provenance denominator window packet)
    (sameMantissa : hsame mantissa mantissa') (sameExponent : hsame exponent exponent')
    (sameLedger : hsame ledger ledger') (sameProvenance : hsame provenance provenance')
    (sameDenominator : hsame denominator denominator') (sameWindow : hsame window window')
    (samePacket : hsame packet packet') :
    DyadicRatCorePacket mantissa' exponent' ledger' provenance' denominator' window' packet' ∧
      Cont exponent' ledger' denominator' ∧ Cont denominator' provenance' window' := by
  cases sameMantissa
  cases sameExponent
  cases sameLedger
  cases sameProvenance
  cases sameDenominator
  cases sameWindow
  cases samePacket
  exact And.intro hD (And.intro hD.right.left hD.right.right.left)

theorem DyadicRatCore_denominator_ledger_transport_window
    {den den' tail route route' : BHist} :
    PositiveUnaryDenominator den -> UnaryHistory tail -> hsame den den' ->
      Cont den tail route -> Cont den' tail route' ->
        PositiveUnaryDenominator den' ∧ PositiveUnaryDenominator (append den' tail) ∧
          hsame route (append den tail) ∧ hsame route' (append den' tail) := by
  intro denPositive tailUnary sameDen routeCont routeCont'
  have denPositive' : PositiveUnaryDenominator den' :=
    PositiveUnaryDenominator_hsame_transport sameDen denPositive
  exact And.intro denPositive'
    (And.intro (PositiveUnaryDenominator_append_unary_tail denPositive' tailUnary)
      (And.intro routeCont routeCont'))

def DyadicRatCoreCarrier (mantissa exponent ledger provenance : BHist) : Prop :=
  RatHistoryCarrier mantissa ∧ PositiveUnaryDenominator exponent ∧ UnaryHistory provenance ∧
    Cont exponent mantissa ledger ∧ UnaryHistory ledger

def DyadicRatCoreClassifier
    (mantissa exponent ledger provenance mantissa' exponent' ledger' provenance' common
      leftScale rightScale : BHist) : Prop :=
  DyadicRatCoreCarrier mantissa exponent ledger provenance ∧
    DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' ∧
      PositiveUnaryDenominator common ∧ Cont exponent common leftScale ∧
        Cont exponent' common rightScale ∧ RatHistoryClassifier leftScale rightScale ∧
          hsame provenance provenance'

theorem DyadicRatCoreCarrier_denominator_transport
    {mantissa exponent ledger provenance mantissa' exponent' ledger' provenance' : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      hsame mantissa mantissa' -> hsame exponent exponent' -> hsame provenance provenance' ->
        Cont exponent' mantissa' ledger' ->
          DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' ∧ hsame ledger ledger' ∧
            RatHistoryCarrier mantissa' ∧ PositiveUnaryDenominator exponent' ∧
              UnaryHistory ledger' := by
  intro carrier sameMantissa sameExponent sameProvenance contLedger'
  have mantissaCarrier : RatHistoryCarrier mantissa := carrier.left
  have exponentPositive : PositiveUnaryDenominator exponent := carrier.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.left
  have contLedger : Cont exponent mantissa ledger := carrier.right.right.right.left
  have mantissaCarrier' : RatHistoryCarrier mantissa' :=
    RatHistoryCarrier_hsame_transport sameMantissa mantissaCarrier
  have exponentPositive' : PositiveUnaryDenominator exponent' :=
    PositiveUnaryDenominator_hsame_transport sameExponent exponentPositive
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have exponentUnary' : UnaryHistory exponent' :=
    (PositiveUnaryDenominator_unary_and_nonempty exponentPositive').left
  have ledgerSame : hsame ledger ledger' :=
    cont_respects_hsame sameExponent sameMantissa contLedger contLedger'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed exponentUnary' (RatHistoryCarrier_iff_positive_denominator.mp
      mantissaCarrier' |> PositiveUnaryDenominator_unary_and_nonempty |>.left) contLedger'
  have carrier' : DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' :=
    And.intro mantissaCarrier'
      (And.intro exponentPositive'
        (And.intro provenanceUnary' (And.intro contLedger' ledgerUnary')))
  exact And.intro carrier'
    (And.intro ledgerSame
      (And.intro mantissaCarrier' (And.intro exponentPositive' ledgerUnary')))

theorem DyadicRatCoreCarrier_monotone_radius_refinement
    {mantissa exponent ledger provenance tail refinedLedger : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      UnaryHistory tail -> Cont ledger tail refinedLedger ->
        PositiveUnaryDenominator (append exponent tail) ∧ UnaryHistory refinedLedger ∧
          Cont ledger tail refinedLedger ∧ hsame refinedLedger (append ledger tail) := by
  intro carrier tailUnary refinementRow
  have exponentPositive : PositiveUnaryDenominator exponent := carrier.right.left
  have exponentTailPositive : PositiveUnaryDenominator (append exponent tail) :=
    PositiveUnaryDenominator_append_unary_tail exponentPositive tailUnary
  have ledgerUnary : UnaryHistory ledger := carrier.right.right.right.right
  have refinedLedgerUnary : UnaryHistory refinedLedger :=
    unary_cont_closed ledgerUnary tailUnary refinementRow
  exact And.intro exponentTailPositive
    (And.intro refinedLedgerUnary (And.intro refinementRow refinementRow))

theorem DyadicRatCoreClassifier_common_exponent_transport
    {mantissa exponent ledger provenance mantissa2 exponent2 ledger2 provenance2 common common'
      scaleLeft scaleRight scaledLeft scaledRight scaleLeft' scaleRight' scaledLeft'
      scaledRight' classifierWindow classifierWindow' : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      DyadicRatCoreCarrier mantissa2 exponent2 ledger2 provenance2 ->
        hsame common common' ->
          Cont exponent common scaleLeft ->
            Cont exponent common' scaleLeft' ->
              Cont exponent2 common scaleRight ->
                Cont exponent2 common' scaleRight' ->
                  Cont mantissa scaleLeft scaledLeft ->
                    Cont mantissa scaleLeft' scaledLeft' ->
                      Cont mantissa2 scaleRight scaledRight ->
                        Cont mantissa2 scaleRight' scaledRight' ->
                          RatHistoryClassifier scaledLeft scaledRight ->
                            Cont scaledLeft scaledRight classifierWindow ->
                              Cont scaledLeft' scaledRight' classifierWindow' ->
                                RatHistoryClassifier scaledLeft' scaledRight' ∧
                                  hsame scaleLeft scaleLeft' ∧
                                    hsame scaleRight scaleRight' ∧
                                      hsame scaledLeft scaledLeft' ∧
                                        hsame scaledRight scaledRight' ∧
                                          hsame classifierWindow classifierWindow' := by
  intro _carrierLeft _carrierRight sameCommon scaleLeftRow scaleLeftRow' scaleRightRow
    scaleRightRow' scaledLeftRow scaledLeftRow' scaledRightRow scaledRightRow' classified
    classifierWindowRow classifierWindowRow'
  have sameScaleLeft : hsame scaleLeft scaleLeft' :=
    cont_respects_hsame (hsame_refl exponent) sameCommon scaleLeftRow scaleLeftRow'
  have sameScaleRight : hsame scaleRight scaleRight' :=
    cont_respects_hsame (hsame_refl exponent2) sameCommon scaleRightRow scaleRightRow'
  have sameScaledLeft : hsame scaledLeft scaledLeft' :=
    cont_respects_hsame (hsame_refl mantissa) sameScaleLeft scaledLeftRow scaledLeftRow'
  have sameScaledRight : hsame scaledRight scaledRight' :=
    cont_respects_hsame (hsame_refl mantissa2) sameScaleRight scaledRightRow
      scaledRightRow'
  have transportedClassifier : RatHistoryClassifier scaledLeft' scaledRight' :=
    RatHistoryClassifier_hsame_transport sameScaledLeft sameScaledRight classified
  have sameClassifierWindow : hsame classifierWindow classifierWindow' :=
    cont_respects_hsame sameScaledLeft sameScaledRight classifierWindowRow classifierWindowRow'
  exact And.intro transportedClassifier
    (And.intro sameScaleLeft
      (And.intro sameScaleRight
        (And.intro sameScaledLeft (And.intro sameScaledRight sameClassifierWindow))))

end BEDC.Derived.DyadicRatCoreUp
