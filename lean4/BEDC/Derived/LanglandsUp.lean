import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LanglandsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LanglandsBHistCorrespondenceCarrier [AskSetup] [PackageSetup]
    (galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧ UnaryHistory galoisAnswer ∧
    UnaryHistory automorphicAnswer ∧ UnaryHistory provenance ∧
      Cont galoisAnswer automorphicAnswer localFactor ∧
        Cont galoisSource automorphicSource ledger ∧
          Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

def LanglandsLFactorClassifier [AskSetup] [PackageSetup]
    (galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' ledger' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
      automorphicAnswer localFactor provenance ledger endpoint bundle pkg ∧
    hsame galoisSource galoisSource' ∧ hsame automorphicSource automorphicSource' ∧
      hsame galoisAnswer galoisAnswer' ∧ hsame automorphicAnswer automorphicAnswer' ∧
        hsame provenance provenance' ∧ PkgSig bundle endpoint' pkg

theorem LanglandsLFactorClassifier_local_factor_stability [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer automorphicAnswer
        localFactor provenance ledger endpoint galoisSource' automorphicSource' galoisAnswer'
        automorphicAnswer' localFactor' provenance' ledger' endpoint' bundle pkg ->
      Cont galoisAnswer' automorphicAnswer' localFactor' ->
        Cont galoisSource' automorphicSource' ledger' ->
          Cont provenance' ledger' endpoint' ->
            LanglandsBHistCorrespondenceCarrier galoisSource' automorphicSource'
                galoisAnswer' automorphicAnswer' localFactor' provenance' ledger' endpoint'
                bundle pkg ∧
              hsame localFactor localFactor' ∧ hsame ledger ledger' ∧
                hsame endpoint endpoint' := by
  intro classified localFactorRow' ledgerRow' endpointRow'
  have carrier := classified.left
  have sameGaloisSource := classified.right.left
  have sameAutomorphicSource := classified.right.right.left
  have sameGaloisAnswer := classified.right.right.right.left
  have sameAutomorphicAnswer := classified.right.right.right.right.left
  have sameProvenance := classified.right.right.right.right.right.left
  have pkgSig' := classified.right.right.right.right.right.right
  have sameLocalFactor : hsame localFactor localFactor' :=
    cont_respects_hsame sameGaloisAnswer sameAutomorphicAnswer
      carrier.right.right.right.right.right.left localFactorRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameGaloisSource sameAutomorphicSource
      carrier.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.left endpointRow'
  exact
    ⟨⟨unary_transport carrier.left sameGaloisSource,
        unary_transport carrier.right.left sameAutomorphicSource,
        unary_transport carrier.right.right.left sameGaloisAnswer,
        unary_transport carrier.right.right.right.left sameAutomorphicAnswer,
        unary_transport carrier.right.right.right.right.left sameProvenance,
        localFactorRow', ledgerRow', endpointRow', pkgSig'⟩,
      sameLocalFactor, sameLedger, sameEndpoint⟩

theorem LanglandsLocalFactor_stability [AskSetup] [PackageSetup]
    {galoisSource automorphicSource galoisAnswer automorphicAnswer localFactor provenance
      ledger endpoint galoisSource' automorphicSource' galoisAnswer' automorphicAnswer'
      localFactor' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LanglandsBHistCorrespondenceCarrier galoisSource automorphicSource galoisAnswer
        automorphicAnswer localFactor provenance ledger endpoint bundle pkg ->
      hsame galoisSource galoisSource' -> hsame automorphicSource automorphicSource' ->
        hsame galoisAnswer galoisAnswer' -> hsame automorphicAnswer automorphicAnswer' ->
          hsame provenance provenance' ->
            Cont galoisAnswer' automorphicAnswer' localFactor' ->
              Cont galoisSource' automorphicSource' ledger' ->
                Cont provenance' ledger' endpoint' -> PkgSig bundle endpoint' pkg ->
                  LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer
                      automorphicAnswer localFactor provenance ledger endpoint galoisSource'
                      automorphicSource' galoisAnswer' automorphicAnswer' localFactor'
                      provenance' ledger' endpoint' bundle pkg ∧
                    LanglandsBHistCorrespondenceCarrier galoisSource' automorphicSource'
                      galoisAnswer' automorphicAnswer' localFactor' provenance' ledger'
                      endpoint' bundle pkg ∧
                    hsame localFactor localFactor' ∧ hsame ledger ledger' ∧
                      hsame endpoint endpoint' := by
  intro carrier sameGaloisSource sameAutomorphicSource sameGaloisAnswer
    sameAutomorphicAnswer sameProvenance localFactorRow' ledgerRow' endpointRow' pkgSig'
  have classified : LanglandsLFactorClassifier galoisSource automorphicSource galoisAnswer
      automorphicAnswer localFactor provenance ledger endpoint galoisSource'
      automorphicSource' galoisAnswer' automorphicAnswer' localFactor' provenance' ledger'
      endpoint' bundle pkg :=
    ⟨carrier, sameGaloisSource, sameAutomorphicSource, sameGaloisAnswer,
      sameAutomorphicAnswer, sameProvenance, pkgSig'⟩
  have sameLocalFactor : hsame localFactor localFactor' :=
    cont_respects_hsame sameGaloisAnswer sameAutomorphicAnswer
      carrier.right.right.right.right.right.left localFactorRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameGaloisSource sameAutomorphicSource
      carrier.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.left endpointRow'
  have transportedCarrier : LanglandsBHistCorrespondenceCarrier galoisSource'
      automorphicSource' galoisAnswer' automorphicAnswer' localFactor' provenance' ledger'
      endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameGaloisSource,
      unary_transport carrier.right.left sameAutomorphicSource,
      unary_transport carrier.right.right.left sameGaloisAnswer,
      unary_transport carrier.right.right.right.left sameAutomorphicAnswer,
      unary_transport carrier.right.right.right.right.left sameProvenance,
      localFactorRow', ledgerRow', endpointRow', pkgSig'⟩
  exact
    ⟨classified, transportedCarrier, sameLocalFactor, sameLedger, sameEndpoint⟩

end BEDC.Derived.LanglandsUp
