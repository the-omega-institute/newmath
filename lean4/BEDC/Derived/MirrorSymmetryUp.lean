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

def MirrorSymmetryPairCarrier [AskSetup] [PackageSetup]
    (symplecticSource derivedSource aModelAnswer bModelAnswer pairLedger transportLedger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory symplecticSource ∧ UnaryHistory derivedSource ∧ UnaryHistory aModelAnswer ∧
    UnaryHistory bModelAnswer ∧ Cont symplecticSource derivedSource transportLedger ∧
      Cont aModelAnswer bModelAnswer pairLedger ∧ Cont transportLedger pairLedger endpoint ∧
        PkgSig bundle endpoint pkg

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

theorem MirrorSymmetryCategorical_stability [AskSetup] [PackageSetup]
    {symplecticSource derivedSource aModelAnswer bModelAnswer pairedAnswer provenance ledger
      endpoint symplecticSource' derivedSource' aModelAnswer' bModelAnswer' pairedAnswer'
      provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MirrorSymmetryBHistPairCarrier symplecticSource derivedSource aModelAnswer bModelAnswer
        pairedAnswer provenance ledger endpoint bundle pkg ->
      hsame symplecticSource symplecticSource' -> hsame derivedSource derivedSource' ->
        hsame aModelAnswer aModelAnswer' -> hsame bModelAnswer bModelAnswer' ->
          hsame provenance provenance' ->
            Cont aModelAnswer' bModelAnswer' pairedAnswer' ->
              Cont symplecticSource' derivedSource' ledger' ->
                Cont provenance' ledger' endpoint' -> PkgSig bundle endpoint' pkg ->
                  MirrorSymmetryCategoricalClassifier symplecticSource derivedSource
                      aModelAnswer bModelAnswer pairedAnswer provenance ledger endpoint
                      symplecticSource' derivedSource' aModelAnswer' bModelAnswer'
                      pairedAnswer' provenance' ledger' endpoint' bundle pkg ∧
                    MirrorSymmetryBHistPairCarrier symplecticSource' derivedSource'
                      aModelAnswer' bModelAnswer' pairedAnswer' provenance' ledger'
                      endpoint' bundle pkg ∧
                    hsame pairedAnswer pairedAnswer' ∧ hsame ledger ledger' ∧
                      hsame endpoint endpoint' := by
  intro carrier sameSymplecticSource sameDerivedSource sameAModelAnswer sameBModelAnswer
    sameProvenance pairedAnswerRow' ledgerRow' endpointRow' pkgSig'
  have classified : MirrorSymmetryCategoricalClassifier symplecticSource derivedSource
      aModelAnswer bModelAnswer pairedAnswer provenance ledger endpoint symplecticSource'
      derivedSource' aModelAnswer' bModelAnswer' pairedAnswer' provenance' ledger' endpoint'
      bundle pkg :=
    ⟨carrier, sameSymplecticSource, sameDerivedSource, sameAModelAnswer, sameBModelAnswer,
      sameProvenance, pkgSig'⟩
  have samePairedAnswer : hsame pairedAnswer pairedAnswer' :=
    cont_respects_hsame sameAModelAnswer sameBModelAnswer
      carrier.right.right.right.right.right.left pairedAnswerRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSymplecticSource sameDerivedSource
      carrier.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      carrier.right.right.right.right.right.right.right.left endpointRow'
  have transportedCarrier : MirrorSymmetryBHistPairCarrier symplecticSource'
      derivedSource' aModelAnswer' bModelAnswer' pairedAnswer' provenance' ledger'
      endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameSymplecticSource,
      unary_transport carrier.right.left sameDerivedSource,
      unary_transport carrier.right.right.left sameAModelAnswer,
      unary_transport carrier.right.right.right.left sameBModelAnswer,
      unary_transport carrier.right.right.right.right.left sameProvenance,
      pairedAnswerRow', ledgerRow', endpointRow', pkgSig'⟩
  exact
    ⟨classified, transportedCarrier, samePairedAnswer, sameLedger, sameEndpoint⟩

theorem MirrorSymmetryPairCarrier_source_certificate_scope [AskSetup] [PackageSetup]
    {symplecticSource derivedSource aModelAnswer bModelAnswer pairLedger transportLedger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MirrorSymmetryPairCarrier symplecticSource derivedSource aModelAnswer bModelAnswer
        pairLedger transportLedger endpoint bundle pkg ->
      UnaryHistory symplecticSource ∧ UnaryHistory derivedSource ∧ UnaryHistory aModelAnswer ∧
        UnaryHistory bModelAnswer ∧ Cont symplecticSource derivedSource transportLedger ∧
          Cont aModelAnswer bModelAnswer pairLedger ∧
            Cont transportLedger pairLedger endpoint ∧
              hsame endpoint (append transportLedger pairLedger) ∧
                PkgSig bundle endpoint pkg := by
  intro ledger
  cases ledger with
  | intro symplecticUnary rest =>
      cases rest with
      | intro derivedUnary rest =>
          cases rest with
          | intro aModelUnary rest =>
              cases rest with
              | intro bModelUnary rest =>
                  cases rest with
                  | intro sourceTransport rest =>
                      cases rest with
                      | intro pairTransport rest =>
                          cases rest with
                          | intro endpointTransport packageSig =>
                              exact
                                ⟨symplecticUnary, derivedUnary, aModelUnary, bModelUnary,
                                  sourceTransport, pairTransport, endpointTransport,
                                  endpointTransport, packageSig⟩

theorem MirrorSymmetryCategoricalClassifier_endpoint_confluence [AskSetup] [PackageSetup]
    {symplecticSource derivedSource aModelAnswer bModelAnswer pairedAnswer provenance ledger
      endpoint symplecticSourceA derivedSourceA aModelAnswerA bModelAnswerA pairedAnswerA
      provenanceA ledgerA endpointA symplecticSourceB derivedSourceB aModelAnswerB
      bModelAnswerB pairedAnswerB provenanceB ledgerB endpointB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MirrorSymmetryCategoricalClassifier symplecticSource derivedSource aModelAnswer
        bModelAnswer pairedAnswer provenance ledger endpoint symplecticSourceA derivedSourceA
        aModelAnswerA bModelAnswerA pairedAnswerA provenanceA ledgerA endpointA bundle pkg ->
      Cont aModelAnswerA bModelAnswerA pairedAnswerA ->
        Cont symplecticSourceA derivedSourceA ledgerA ->
          Cont provenanceA ledgerA endpointA ->
            MirrorSymmetryCategoricalClassifier symplecticSource derivedSource aModelAnswer
                bModelAnswer pairedAnswer provenance ledger endpoint symplecticSourceB
                derivedSourceB aModelAnswerB bModelAnswerB pairedAnswerB provenanceB ledgerB
                endpointB bundle pkg ->
              Cont aModelAnswerB bModelAnswerB pairedAnswerB ->
                Cont symplecticSourceB derivedSourceB ledgerB ->
                  Cont provenanceB ledgerB endpointB ->
                    hsame pairedAnswerA pairedAnswerB ∧ hsame ledgerA ledgerB ∧
                      hsame endpointA endpointB := by
  intro classifiedA pairedAnswerRowA ledgerRowA endpointRowA classifiedB pairedAnswerRowB
    ledgerRowB endpointRowB
  have branchA :=
    MirrorSymmetryCategoricalClassifier_categorical_stability classifiedA pairedAnswerRowA
      ledgerRowA endpointRowA
  have branchB :=
    MirrorSymmetryCategoricalClassifier_categorical_stability classifiedB pairedAnswerRowB
      ledgerRowB endpointRowB
  have samePairedAnswerA : hsame pairedAnswer pairedAnswerA := branchA.right.left
  have sameLedgerA : hsame ledger ledgerA := branchA.right.right.left
  have sameEndpointA : hsame endpoint endpointA := branchA.right.right.right
  have samePairedAnswerB : hsame pairedAnswer pairedAnswerB := branchB.right.left
  have sameLedgerB : hsame ledger ledgerB := branchB.right.right.left
  have sameEndpointB : hsame endpoint endpointB := branchB.right.right.right
  exact
    ⟨hsame_trans (hsame_symm samePairedAnswerA) samePairedAnswerB,
      hsame_trans (hsame_symm sameLedgerA) sameLedgerB,
      hsame_trans (hsame_symm sameEndpointA) sameEndpointB⟩

end BEDC.Derived.MirrorSymmetryUp
