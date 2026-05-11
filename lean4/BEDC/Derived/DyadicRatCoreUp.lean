import BEDC.Derived.RatUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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

theorem DyadicRatCoreCarrier_arithmetic_window_stability
    {m0 e0 l0 p0 m1 e1 l1 p1 m0' e0' l0' p0' m1' e1' l1' p1' left left' op op'
      window window' : BHist} :
    DyadicRatCoreCarrier m0 e0 l0 p0 ->
      DyadicRatCoreCarrier m1 e1 l1 p1 ->
        hsame m0 m0' ->
          hsame e0 e0' ->
            hsame p0 p0' ->
              hsame m1 m1' ->
                hsame e1 e1' ->
                  hsame p1 p1' ->
                    Cont e0' m0' l0' ->
                      Cont e1' m1' l1' ->
                        Cont l0 l1 left ->
                          Cont l0' l1' left' ->
                            Cont left p0 op ->
                              Cont left' p0' op' ->
                                Cont op p1 window ->
                                  Cont op' p1' window' ->
                                    DyadicRatCoreCarrier m0' e0' l0' p0' ∧
                                      DyadicRatCoreCarrier m1' e1' l1' p1' ∧
                                        hsame l0 l0' ∧
                                          hsame l1 l1' ∧
                                            hsame left left' ∧
                                              hsame op op' ∧ hsame window window' := by
  intro carrier0 carrier1 sameM0 sameE0 sameP0 sameM1 sameE1 sameP1 rowL0' rowL1'
    rowLeft rowLeft' rowOp rowOp' rowWindow rowWindow'
  have transported0 :=
    DyadicRatCoreCarrier_denominator_transport carrier0 sameM0 sameE0 sameP0 rowL0'
  have transported1 :=
    DyadicRatCoreCarrier_denominator_transport carrier1 sameM1 sameE1 sameP1 rowL1'
  have carrier0' : DyadicRatCoreCarrier m0' e0' l0' p0' := transported0.left
  have carrier1' : DyadicRatCoreCarrier m1' e1' l1' p1' := transported1.left
  have sameL0 : hsame l0 l0' := transported0.right.left
  have sameL1 : hsame l1 l1' := transported1.right.left
  have sameLeft : hsame left left' :=
    cont_respects_hsame sameL0 sameL1 rowLeft rowLeft'
  have sameOp : hsame op op' :=
    cont_respects_hsame sameLeft sameP0 rowOp rowOp'
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameOp sameP1 rowWindow rowWindow'
  exact And.intro carrier0'
    (And.intro carrier1'
      (And.intro sameL0
        (And.intro sameL1
          (And.intro sameLeft (And.intro sameOp sameWindow)))))

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

def DyadicRatCoreArithmeticWindow
    (mantissa0 mantissa1 exponent0 exponent1 ledger0 ledger1 provenance0 provenance1 sum neg
      diff prod window : BHist) : Prop :=
  UnaryHistory mantissa0 ∧
    UnaryHistory mantissa1 ∧
      UnaryHistory exponent0 ∧
        UnaryHistory exponent1 ∧
          Cont exponent0 mantissa0 ledger0 ∧
            Cont exponent1 mantissa1 ledger1 ∧
              Cont ledger0 provenance0 sum ∧
                Cont ledger1 provenance1 neg ∧ Cont sum neg diff ∧ Cont diff prod window

theorem DyadicRatCoreArithmeticWindow_transport_stability
    {mantissa0 mantissa1 exponent0 exponent1 ledger0 ledger1 provenance0 provenance1 sum neg
      diff prod window mantissa0' mantissa1' exponent0' exponent1' ledger0' ledger1'
      provenance0' provenance1' sum' neg' diff' prod' window' : BHist} :
    DyadicRatCoreArithmeticWindow mantissa0 mantissa1 exponent0 exponent1 ledger0 ledger1
        provenance0 provenance1 sum neg diff prod window ->
      hsame mantissa0 mantissa0' ->
        hsame mantissa1 mantissa1' ->
          hsame exponent0 exponent0' ->
            hsame exponent1 exponent1' ->
              hsame ledger0 ledger0' ->
                hsame ledger1 ledger1' ->
                  hsame provenance0 provenance0' ->
                    hsame provenance1 provenance1' ->
                      hsame sum sum' ->
                        hsame neg neg' ->
                          hsame diff diff' ->
                            hsame prod prod' ->
                              hsame window window' ->
                                DyadicRatCoreArithmeticWindow mantissa0' mantissa1'
                                    exponent0' exponent1' ledger0' ledger1' provenance0'
                                    provenance1' sum' neg' diff' prod' window' ∧
                                  Cont sum' neg' diff' ∧ Cont diff' prod' window' := by
  intro windowData sameMantissa0 sameMantissa1 sameExponent0 sameExponent1 sameLedger0
    sameLedger1 sameProvenance0 sameProvenance1 sameSum sameNeg sameDiff sameProd sameWindow
  cases windowData with
  | intro mantissa0Unary windowRest =>
      cases windowRest with
      | intro mantissa1Unary windowRest =>
          cases windowRest with
          | intro exponent0Unary windowRest =>
              cases windowRest with
              | intro exponent1Unary windowRest =>
                  cases windowRest with
                  | intro ledger0Row windowRest =>
                      cases windowRest with
                      | intro ledger1Row windowRest =>
                          cases windowRest with
                          | intro sumRow windowRest =>
                              cases windowRest with
                              | intro negRow windowRest =>
                                  cases windowRest with
                                  | intro diffRow prodRow =>
                                      have mantissa0Unary' : UnaryHistory mantissa0' :=
                                        unary_transport mantissa0Unary sameMantissa0
                                      have mantissa1Unary' : UnaryHistory mantissa1' :=
                                        unary_transport mantissa1Unary sameMantissa1
                                      have exponent0Unary' : UnaryHistory exponent0' :=
                                        unary_transport exponent0Unary sameExponent0
                                      have exponent1Unary' : UnaryHistory exponent1' :=
                                        unary_transport exponent1Unary sameExponent1
                                      have ledger0Row' : Cont exponent0' mantissa0' ledger0' :=
                                        cont_hsame_transport sameExponent0 sameMantissa0
                                          sameLedger0 ledger0Row
                                      have ledger1Row' : Cont exponent1' mantissa1' ledger1' :=
                                        cont_hsame_transport sameExponent1 sameMantissa1
                                          sameLedger1 ledger1Row
                                      have sumRow' : Cont ledger0' provenance0' sum' :=
                                        cont_hsame_transport sameLedger0 sameProvenance0 sameSum
                                          sumRow
                                      have negRow' : Cont ledger1' provenance1' neg' :=
                                        cont_hsame_transport sameLedger1 sameProvenance1 sameNeg
                                          negRow
                                      have diffRow' : Cont sum' neg' diff' :=
                                        cont_hsame_transport sameSum sameNeg sameDiff diffRow
                                      have prodRow' : Cont diff' prod' window' :=
                                        cont_hsame_transport sameDiff sameProd sameWindow prodRow
                                      exact And.intro
                                        (And.intro mantissa0Unary'
                                          (And.intro mantissa1Unary'
                                            (And.intro exponent0Unary'
                                              (And.intro exponent1Unary'
                                                (And.intro ledger0Row'
                                                  (And.intro ledger1Row'
                                                    (And.intro sumRow'
                                                      (And.intro negRow'
                                                        (And.intro diffRow' prodRow')))))))))
                                        (And.intro diffRow' prodRow')

theorem DyadicRatCoreCarrier_common_exponent_window_exactness
    {mantissa exponent ledger provenance mantissa' exponent' ledger' provenance' common scale
      scale' left right classifierWindow : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' ->
        PositiveUnaryDenominator common ->
          Cont exponent common scale ->
            Cont exponent' common scale' ->
              Cont mantissa scale left ->
                Cont mantissa' scale' right ->
                  Cont left right classifierWindow ->
                    UnaryHistory scale ∧ UnaryHistory scale' ∧ UnaryHistory left ∧
                      UnaryHistory right ∧ UnaryHistory classifierWindow ∧
                        hsame scale (append exponent common) ∧
                          hsame scale' (append exponent' common) ∧
                            hsame classifierWindow (append left right) := by
  intro carrier carrier' commonPositive scaleRow scaleRow' leftRow rightRow classifierRow
  have exponentUnary : UnaryHistory exponent :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier.right.left).left
  have exponentUnary' : UnaryHistory exponent' :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier'.right.left).left
  have commonUnary : UnaryHistory common :=
    (PositiveUnaryDenominator_unary_and_nonempty commonPositive).left
  have scaleUnary : UnaryHistory scale :=
    unary_cont_closed exponentUnary commonUnary scaleRow
  have scaleUnary' : UnaryHistory scale' :=
    unary_cont_closed exponentUnary' commonUnary scaleRow'
  have mantissaUnary : UnaryHistory mantissa :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrier.left)).left
  have mantissaUnary' : UnaryHistory mantissa' :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrier'.left)).left
  have leftUnary : UnaryHistory left :=
    unary_cont_closed mantissaUnary scaleUnary leftRow
  have rightUnary : UnaryHistory right :=
    unary_cont_closed mantissaUnary' scaleUnary' rightRow
  have classifierUnary : UnaryHistory classifierWindow :=
    unary_cont_closed leftUnary rightUnary classifierRow
  exact And.intro scaleUnary
    (And.intro scaleUnary'
      (And.intro leftUnary
        (And.intro rightUnary
          (And.intro classifierUnary
            (And.intro scaleRow (And.intro scaleRow' classifierRow))))))

end BEDC.Derived.DyadicRatCoreUp
