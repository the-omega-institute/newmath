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
