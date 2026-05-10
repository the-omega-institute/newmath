import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PersistentHomUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PersistentHomFiltrationCarrier [AskSetup] [PackageSetup]
    (indexSpine complexRows homologyRows boundaryRows persistenceRows route provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory indexSpine ∧ UnaryHistory complexRows ∧ UnaryHistory homologyRows ∧
    UnaryHistory boundaryRows ∧ Cont indexSpine complexRows route ∧
      Cont boundaryRows homologyRows persistenceRows ∧ Cont route persistenceRows provenance ∧
        Cont provenance persistenceRows endpoint ∧ PkgSig bundle endpoint pkg

theorem PersistentHomFiltrationCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {indexRow stageRows homologyRows boundaryRows persistenceRows barcodeRows routeLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory indexRow ->
      UnaryHistory stageRows ->
        UnaryHistory homologyRows ->
          UnaryHistory barcodeRows ->
            UnaryHistory provenance ->
              Cont indexRow stageRows boundaryRows ->
                Cont boundaryRows homologyRows persistenceRows ->
                  Cont persistenceRows barcodeRows routeLedger ->
                    Cont provenance routeLedger endpoint ->
                      PkgSig bundle endpoint pkg ->
                        UnaryHistory boundaryRows ∧ UnaryHistory persistenceRows ∧
                          UnaryHistory routeLedger ∧ UnaryHistory endpoint ∧
                            hsame boundaryRows (append indexRow stageRows) ∧
                              hsame persistenceRows (append boundaryRows homologyRows) ∧
                                hsame routeLedger (append persistenceRows barcodeRows) ∧
                                  hsame endpoint (append provenance routeLedger) ∧
                                    PkgSig bundle endpoint pkg := by
  intro indexUnary stageUnary homologyUnary barcodeUnary provenanceUnary boundaryRow
    persistenceRow routeRow endpointRow pkgSig
  have boundaryUnary : UnaryHistory boundaryRows :=
    unary_cont_closed indexUnary stageUnary boundaryRow
  have persistenceUnary : UnaryHistory persistenceRows :=
    unary_cont_closed boundaryUnary homologyUnary persistenceRow
  have routeUnary : UnaryHistory routeLedger :=
    unary_cont_closed persistenceUnary barcodeUnary routeRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary routeUnary endpointRow
  exact
    And.intro boundaryUnary
      (And.intro persistenceUnary
        (And.intro routeUnary
          (And.intro endpointUnary
            (And.intro boundaryRow
              (And.intro persistenceRow
                  (And.intro routeRow
                    (And.intro endpointRow pkgSig)))))))

theorem PersistentHomFiltrationCarrier_classifier_stability [AskSetup] [PackageSetup]
    {indexSpine complexRows homologyRows boundaryRows persistenceRows route provenance endpoint
      indexSpine' complexRows' homologyRows' boundaryRows' persistenceRows' route' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PersistentHomFiltrationCarrier indexSpine complexRows homologyRows boundaryRows
        persistenceRows route provenance endpoint bundle pkg ->
      hsame indexSpine indexSpine' ->
        hsame complexRows complexRows' ->
          hsame homologyRows homologyRows' ->
            hsame boundaryRows boundaryRows' ->
              Cont indexSpine' complexRows' route' ->
                Cont boundaryRows' homologyRows' persistenceRows' ->
                  Cont route' persistenceRows' provenance' ->
                    Cont provenance' persistenceRows' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        PersistentHomFiltrationCarrier indexSpine' complexRows' homologyRows'
                            boundaryRows' persistenceRows' route' provenance' endpoint'
                            bundle pkg ∧
                          hsame route route' ∧ hsame persistenceRows persistenceRows' ∧
                            hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameIndex sameComplex sameHomology sameBoundary routeCont' persistenceCont'
    provenanceCont' endpointCont' endpointPkg'
  have routeSame : hsame route route' :=
    cont_respects_hsame sameIndex sameComplex
      carrier.right.right.right.right.left routeCont'
  have persistenceSame : hsame persistenceRows persistenceRows' :=
    cont_respects_hsame sameBoundary sameHomology
      carrier.right.right.right.right.right.left persistenceCont'
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame routeSame persistenceSame
      carrier.right.right.right.right.right.right.left provenanceCont'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame provenanceSame persistenceSame
      carrier.right.right.right.right.right.right.right.left endpointCont'
  have transportedCarrier :
      PersistentHomFiltrationCarrier indexSpine' complexRows' homologyRows' boundaryRows'
        persistenceRows' route' provenance' endpoint' bundle pkg :=
    ⟨unary_transport carrier.left sameIndex,
      unary_transport carrier.right.left sameComplex,
      unary_transport carrier.right.right.left sameHomology,
      unary_transport carrier.right.right.right.left sameBoundary,
      routeCont',
      persistenceCont',
      provenanceCont',
      endpointCont',
      endpointPkg'⟩
  exact
    ⟨transportedCarrier, routeSame, persistenceSame, provenanceSame, endpointSame⟩

end BEDC.Derived.PersistentHomUp
