import BEDC.Derived.RatUp
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

def DyadicRatCoreCarrier [AskSetup] [PackageSetup]
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
    DyadicRatCoreCarrier mantissa exponent ledger provenance endpoint bundle pkg ->
      hsame mantissa mantissa' ->
        hsame exponent exponent' ->
          hsame ledger ledger' ->
            Cont exponent' ledger' provenance' ->
              Cont provenance' mantissa' endpoint' ->
                PkgSig bundle endpoint' pkg ->
                  DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' endpoint'
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

end BEDC.Derived.DyadicRatCoreUp
