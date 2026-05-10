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
    (index stage homology boundary persistence barcode route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory stage ∧ UnaryHistory homology ∧
    UnaryHistory persistence ∧ UnaryHistory barcode ∧ UnaryHistory provenance ∧
      Cont stage homology boundary ∧ Cont boundary persistence route ∧
        Cont route barcode endpoint ∧ PkgSig bundle endpoint pkg

theorem PersistentHomFiltrationLedger_exactness [AskSetup] [PackageSetup]
    {index stage homology boundary persistence barcode route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PersistentHomFiltrationCarrier index stage homology boundary persistence barcode route
        provenance endpoint bundle pkg ->
      UnaryHistory index ∧ UnaryHistory stage ∧ UnaryHistory homology ∧
        UnaryHistory boundary ∧ UnaryHistory persistence ∧ UnaryHistory barcode ∧
          Cont stage homology boundary ∧ Cont boundary persistence route ∧
            Cont route barcode endpoint ∧ PkgSig bundle endpoint pkg ∧
              hsame endpoint (append route barcode) := by
  intro carrier
  have indexUnary : UnaryHistory index :=
    carrier.left
  have stageUnary : UnaryHistory stage :=
    carrier.right.left
  have homologyUnary : UnaryHistory homology :=
    carrier.right.right.left
  have persistenceUnary : UnaryHistory persistence :=
    carrier.right.right.right.left
  have barcodeUnary : UnaryHistory barcode :=
    carrier.right.right.right.right.left
  have boundaryCont : Cont stage homology boundary :=
    carrier.right.right.right.right.right.right.left
  have routeCont : Cont boundary persistence route :=
    carrier.right.right.right.right.right.right.right.left
  have endpointCont : Cont route barcode endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed stageUnary homologyUnary boundaryCont
  exact And.intro indexUnary
    (And.intro stageUnary
      (And.intro homologyUnary
        (And.intro boundaryUnary
          (And.intro persistenceUnary
            (And.intro barcodeUnary
              (And.intro boundaryCont
                (And.intro routeCont
                  (And.intro endpointCont
                    (And.intro pkgSig endpointCont)))))))))

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

end BEDC.Derived.PersistentHomUp
