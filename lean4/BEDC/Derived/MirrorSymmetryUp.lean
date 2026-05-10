import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MirrorSymmetryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MirrorSymmetryBHistPairCarrier [AskSetup] [PackageSetup]
    (symplecticSource derivedSource aModelAnswer bModelAnswer pairedAnswer provenance ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory symplecticSource ∧ UnaryHistory derivedSource ∧ UnaryHistory aModelAnswer ∧
    UnaryHistory bModelAnswer ∧ UnaryHistory provenance ∧
      Cont aModelAnswer bModelAnswer pairedAnswer ∧
        Cont symplecticSource derivedSource ledger ∧
          Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

def MirrorSymmetryCategoricalClassifier [AskSetup] [PackageSetup]
    (symplecticSource derivedSource aModelAnswer bModelAnswer pairedAnswer provenance ledger
      endpoint symplecticSource' derivedSource' aModelAnswer' bModelAnswer' pairedAnswer'
      provenance' ledger' endpoint' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MirrorSymmetryBHistPairCarrier symplecticSource derivedSource aModelAnswer bModelAnswer
      pairedAnswer provenance ledger endpoint bundle pkg ∧
    hsame symplecticSource symplecticSource' ∧ hsame derivedSource derivedSource' ∧
      hsame aModelAnswer aModelAnswer' ∧ hsame bModelAnswer bModelAnswer' ∧
        hsame provenance provenance' ∧ PkgSig bundle endpoint' pkg

theorem MirrorSymmetryCategoricalClassifier_categorical_stability [AskSetup] [PackageSetup]
    {symplecticSource derivedSource aModelAnswer bModelAnswer pairedAnswer provenance ledger
      endpoint symplecticSource' derivedSource' aModelAnswer' bModelAnswer' pairedAnswer'
      provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MirrorSymmetryCategoricalClassifier symplecticSource derivedSource aModelAnswer
        bModelAnswer pairedAnswer provenance ledger endpoint symplecticSource' derivedSource'
        aModelAnswer' bModelAnswer' pairedAnswer' provenance' ledger' endpoint' bundle pkg ->
      Cont aModelAnswer' bModelAnswer' pairedAnswer' ->
        Cont symplecticSource' derivedSource' ledger' ->
          Cont provenance' ledger' endpoint' ->
            MirrorSymmetryBHistPairCarrier symplecticSource' derivedSource' aModelAnswer'
                bModelAnswer' pairedAnswer' provenance' ledger' endpoint' bundle pkg ∧
              hsame pairedAnswer pairedAnswer' ∧ hsame ledger ledger' ∧
                hsame endpoint endpoint' := by
  intro classified pairedAnswerRow' ledgerRow' endpointRow'
  have carrier := classified.left
  have sameSymplecticSource := classified.right.left
  have sameDerivedSource := classified.right.right.left
  have sameAModelAnswer := classified.right.right.right.left
  have sameBModelAnswer := classified.right.right.right.right.left
  have sameProvenance := classified.right.right.right.right.right.left
  have pkgSig' := classified.right.right.right.right.right.right
  have samePairedAnswer : hsame pairedAnswer pairedAnswer' :=
    cont_respects_hsame sameAModelAnswer sameBModelAnswer
      carrier.right.right.right.right.right.left pairedAnswerRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSymplecticSource sameDerivedSource
      carrier.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.left endpointRow'
  exact
    ⟨⟨unary_transport carrier.left sameSymplecticSource,
        unary_transport carrier.right.left sameDerivedSource,
        unary_transport carrier.right.right.left sameAModelAnswer,
        unary_transport carrier.right.right.right.left sameBModelAnswer,
        unary_transport carrier.right.right.right.right.left sameProvenance,
        pairedAnswerRow', ledgerRow', endpointRow', pkgSig'⟩,
      samePairedAnswer, sameLedger, sameEndpoint⟩

def MirrorSymmetryPairCarrier
    (symplecticSource derivedSource aModelRows bModelRows pairRows sourcePair observed :
      BHist) : Prop :=
  UnaryHistory symplecticSource ∧ UnaryHistory derivedSource ∧ UnaryHistory aModelRows ∧
    UnaryHistory bModelRows ∧ UnaryHistory pairRows ∧ UnaryHistory sourcePair ∧
      UnaryHistory observed ∧ Cont symplecticSource derivedSource sourcePair ∧
        Cont aModelRows bModelRows pairRows ∧ Cont sourcePair pairRows observed

theorem MirrorSymmetryPairCarrier_categorical_stability
    {symplecticSource derivedSource aModelRows bModelRows pairRows sourcePair observed
      symplecticSource' derivedSource' aModelRows' bModelRows' pairRows' sourcePair'
      observed' : BHist} :
    MirrorSymmetryPairCarrier symplecticSource derivedSource aModelRows bModelRows pairRows
        sourcePair observed ->
      hsame symplecticSource symplecticSource' ->
        hsame derivedSource derivedSource' ->
          hsame aModelRows aModelRows' ->
            hsame bModelRows bModelRows' ->
              Cont symplecticSource' derivedSource' sourcePair' ->
                Cont aModelRows' bModelRows' pairRows' ->
                  Cont sourcePair' pairRows' observed' ->
                    MirrorSymmetryPairCarrier symplecticSource' derivedSource' aModelRows'
                        bModelRows' pairRows' sourcePair' observed' ∧
                      hsame sourcePair sourcePair' ∧ hsame pairRows pairRows' ∧
                        hsame observed observed' := by
  intro carrier sameSymplecticSource sameDerivedSource sameAModelRows sameBModelRows
  intro sourcePairRow' pairRowsRow' observedRow'
  have symplecticSourceUnary' : UnaryHistory symplecticSource' :=
    unary_transport carrier.left sameSymplecticSource
  have derivedSourceUnary' : UnaryHistory derivedSource' :=
    unary_transport carrier.right.left sameDerivedSource
  have aModelRowsUnary' : UnaryHistory aModelRows' :=
    unary_transport carrier.right.right.left sameAModelRows
  have bModelRowsUnary' : UnaryHistory bModelRows' :=
    unary_transport carrier.right.right.right.left sameBModelRows
  have sourcePairUnary' : UnaryHistory sourcePair' :=
    unary_cont_closed symplecticSourceUnary' derivedSourceUnary' sourcePairRow'
  have pairRowsUnary' : UnaryHistory pairRows' :=
    unary_cont_closed aModelRowsUnary' bModelRowsUnary' pairRowsRow'
  have observedUnary' : UnaryHistory observed' :=
    unary_cont_closed sourcePairUnary' pairRowsUnary' observedRow'
  have sameSourcePair : hsame sourcePair sourcePair' :=
    cont_respects_hsame sameSymplecticSource sameDerivedSource
      carrier.right.right.right.right.right.right.right.left sourcePairRow'
  have samePairRows : hsame pairRows pairRows' :=
    cont_respects_hsame sameAModelRows sameBModelRows
      carrier.right.right.right.right.right.right.right.right.left pairRowsRow'
  have sameObserved : hsame observed observed' :=
    cont_respects_hsame sameSourcePair samePairRows
      carrier.right.right.right.right.right.right.right.right.right observedRow'
  exact
    ⟨⟨symplecticSourceUnary', derivedSourceUnary', aModelRowsUnary', bModelRowsUnary',
      pairRowsUnary', sourcePairUnary', observedUnary', sourcePairRow', pairRowsRow',
      observedRow'⟩,
      sameSourcePair, samePairRows, sameObserved⟩

end BEDC.Derived.MirrorSymmetryUp
