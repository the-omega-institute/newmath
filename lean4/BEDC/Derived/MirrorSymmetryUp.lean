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

end BEDC.Derived.MirrorSymmetryUp
