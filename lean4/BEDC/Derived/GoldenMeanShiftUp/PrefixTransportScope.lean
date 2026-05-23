import BEDC.Derived.GoldenMeanShiftUp

namespace BEDC.Derived.GoldenMeanShiftUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem GoldenMeanShiftCarrier_prefix_transport_scope [AskSetup] [PackageSetup]
    {window zeroWitness adjacencyLedger provenance ledger endpoint prefixWindow prefixAdjacency
      prefixLedger prefixEndpoint transportedWindow transportedZero transportedAdjacency
      transportedProvenance transportedLedger transportedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoldenMeanShiftCarrier window zeroWitness adjacencyLedger provenance ledger endpoint
        bundle pkg ->
      UnaryHistory prefixWindow ->
        Cont prefixWindow zeroWitness prefixAdjacency ->
          Cont prefixAdjacency provenance prefixLedger ->
            Cont prefixLedger zeroWitness prefixEndpoint ->
              PkgSig bundle prefixEndpoint pkg ->
                hsame prefixWindow transportedWindow ->
                  hsame zeroWitness transportedZero ->
                    hsame prefixAdjacency transportedAdjacency ->
                      hsame provenance transportedProvenance ->
                        hsame prefixLedger transportedLedger ->
                          hsame prefixEndpoint transportedEndpoint ->
                            Cont transportedWindow transportedZero transportedAdjacency ->
                              Cont transportedAdjacency transportedProvenance
                                  transportedLedger ->
                                Cont transportedLedger transportedZero transportedEndpoint ->
                                  PkgSig bundle transportedEndpoint pkg ->
                                    GoldenMeanShiftCarrier transportedWindow transportedZero
                                        transportedAdjacency transportedProvenance
                                        transportedLedger transportedEndpoint bundle pkg ∧
                                      hsame transportedEndpoint prefixEndpoint := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier prefixUnary prefixFirst prefixSecond prefixThird prefixPkg
  intro sameWindow sameZero sameAdjacency sameProvenance sameLedger sameEndpoint
  intro transportedFirst transportedSecond transportedThird transportedPkg
  obtain ⟨_windowUnary, zeroUnary, _adjacencyUnary, provenanceUnary, _ledgerUnary,
    _firstCont, _secondCont, _thirdCont, _endpointPkg⟩ := carrier
  have prefixAdjacencyUnary : UnaryHistory prefixAdjacency :=
    unary_cont_closed prefixUnary zeroUnary prefixFirst
  have prefixLedgerUnary : UnaryHistory prefixLedger :=
    unary_cont_closed prefixAdjacencyUnary provenanceUnary prefixSecond
  have prefixCarrier :
      GoldenMeanShiftCarrier prefixWindow zeroWitness prefixAdjacency provenance prefixLedger
          prefixEndpoint bundle pkg :=
    ⟨prefixUnary, zeroUnary, prefixAdjacencyUnary, provenanceUnary, prefixLedgerUnary,
      prefixFirst, prefixSecond, prefixThird, prefixPkg⟩
  have transported :=
    GoldenMeanShiftCarrier_local_stability
      (window := prefixWindow) (zeroWitness := zeroWitness)
      (adjacencyLedger := prefixAdjacency) (provenance := provenance)
      (ledger := prefixLedger) (endpoint := prefixEndpoint)
      (window' := transportedWindow) (zeroWitness' := transportedZero)
      (adjacencyLedger' := transportedAdjacency) (provenance' := transportedProvenance)
      (ledger' := transportedLedger) (endpoint' := transportedEndpoint) (bundle := bundle)
      (pkg := pkg) prefixCarrier sameWindow sameZero sameAdjacency sameProvenance sameLedger
      sameEndpoint transportedFirst transportedSecond transportedThird transportedPkg
  exact ⟨transported.left, hsame_symm transported.right⟩

end BEDC.Derived.GoldenMeanShiftUp
