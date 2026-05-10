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

def LanglandsCorrespondenceCarrier
    (galoisSource automorphicSource galoisAnswers automorphicAnswers localFactors sourcePair
      observed : BHist) : Prop :=
  UnaryHistory galoisSource ∧ UnaryHistory automorphicSource ∧ UnaryHistory galoisAnswers ∧
    UnaryHistory automorphicAnswers ∧ UnaryHistory localFactors ∧ UnaryHistory sourcePair ∧
      UnaryHistory observed ∧ Cont galoisSource automorphicSource sourcePair ∧
        Cont galoisAnswers automorphicAnswers localFactors ∧
          Cont sourcePair localFactors observed

theorem LanglandsCorrespondenceCarrier_local_factor_stability
    {galoisSource automorphicSource galoisAnswers automorphicAnswers localFactors sourcePair
      observed galoisSource' automorphicSource' galoisAnswers' automorphicAnswers'
      localFactors' sourcePair' observed' : BHist} :
    LanglandsCorrespondenceCarrier galoisSource automorphicSource galoisAnswers
        automorphicAnswers localFactors sourcePair observed ->
      hsame galoisSource galoisSource' ->
        hsame automorphicSource automorphicSource' ->
          hsame galoisAnswers galoisAnswers' ->
            hsame automorphicAnswers automorphicAnswers' ->
              Cont galoisSource' automorphicSource' sourcePair' ->
                Cont galoisAnswers' automorphicAnswers' localFactors' ->
                  Cont sourcePair' localFactors' observed' ->
                    LanglandsCorrespondenceCarrier galoisSource' automorphicSource'
                        galoisAnswers' automorphicAnswers' localFactors' sourcePair'
                        observed' ∧
                      hsame sourcePair sourcePair' ∧ hsame localFactors localFactors' ∧
                        hsame observed observed' := by
  intro carrier sameGaloisSource sameAutomorphicSource sameGaloisAnswers
  intro sameAutomorphicAnswers sourcePairRow' localFactorsRow' observedRow'
  have galoisSourceUnary' : UnaryHistory galoisSource' :=
    unary_transport carrier.left sameGaloisSource
  have automorphicSourceUnary' : UnaryHistory automorphicSource' :=
    unary_transport carrier.right.left sameAutomorphicSource
  have galoisAnswersUnary' : UnaryHistory galoisAnswers' :=
    unary_transport carrier.right.right.left sameGaloisAnswers
  have automorphicAnswersUnary' : UnaryHistory automorphicAnswers' :=
    unary_transport carrier.right.right.right.left sameAutomorphicAnswers
  have sourcePairUnary' : UnaryHistory sourcePair' :=
    unary_cont_closed galoisSourceUnary' automorphicSourceUnary' sourcePairRow'
  have localFactorsUnary' : UnaryHistory localFactors' :=
    unary_cont_closed galoisAnswersUnary' automorphicAnswersUnary' localFactorsRow'
  have observedUnary' : UnaryHistory observed' :=
    unary_cont_closed sourcePairUnary' localFactorsUnary' observedRow'
  have sameSourcePair : hsame sourcePair sourcePair' :=
    cont_respects_hsame sameGaloisSource sameAutomorphicSource
      carrier.right.right.right.right.right.right.right.left sourcePairRow'
  have sameLocalFactors : hsame localFactors localFactors' :=
    cont_respects_hsame sameGaloisAnswers sameAutomorphicAnswers
      carrier.right.right.right.right.right.right.right.right.left localFactorsRow'
  have sameObserved : hsame observed observed' :=
    cont_respects_hsame sameSourcePair sameLocalFactors
      carrier.right.right.right.right.right.right.right.right.right observedRow'
  exact
    ⟨⟨galoisSourceUnary', automorphicSourceUnary', galoisAnswersUnary',
      automorphicAnswersUnary', localFactorsUnary', sourcePairUnary', observedUnary',
      sourcePairRow', localFactorsRow', observedRow'⟩,
      sameSourcePair, sameLocalFactors, sameObserved⟩

end BEDC.Derived.LanglandsUp
