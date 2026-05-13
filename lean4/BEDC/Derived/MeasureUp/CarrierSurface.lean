import BEDC.Derived.MeasureUp
import BEDC.FKernel.Ask

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MeasureSigmaAlgebraCarrierSurface [AskSetup] [PackageSetup]
    (emptyEvent binaryUnion countableUnion complement disjointReadback realValue transport
      ledger classifier provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MeasureZeroBHistCarrier emptyEvent ∧ MeasureZeroBHistCarrier binaryUnion ∧
    MeasureZeroBHistCarrier countableUnion ∧ MeasureZeroBHistCarrier complement ∧
      MeasureZeroBHistCarrier disjointReadback ∧ MeasureZeroBHistCarrier realValue ∧
        MeasureZeroBHistCarrier transport ∧ Cont emptyEvent binaryUnion countableUnion ∧
          Cont complement disjointReadback ledger ∧
            hsame classifier (append realValue ledger) ∧ PkgSig bundle provenance pkg

theorem MeasureSigmaAlgebraCarrierSurface_rows [AskSetup] [PackageSetup]
    {emptyEvent binaryUnion countableUnion complement disjointReadback realValue transport ledger
      classifier provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MeasureSigmaAlgebraCarrierSurface emptyEvent binaryUnion countableUnion complement
        disjointReadback realValue transport ledger classifier provenance bundle pkg ->
      Cont ledger transport endpoint ->
        UnaryHistory endpoint ∧ hsame classifier (append realValue ledger) ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro surface ledgerTransportEndpoint
  obtain ⟨_emptyCarrier, _binaryCarrier, _countableCarrier, complementCarrier,
    disjointCarrier, _realCarrier, transportCarrier, _emptyBinaryCountable,
    complementDisjointLedger, classifierRow, provenancePkg⟩ := surface
  have complementUnary : UnaryHistory complement :=
    unary_transport unary_empty (hsame_symm complementCarrier)
  have disjointUnary : UnaryHistory disjointReadback :=
    unary_transport unary_empty (hsame_symm disjointCarrier)
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed complementUnary disjointUnary complementDisjointLedger
  have transportUnary : UnaryHistory transport :=
    unary_transport unary_empty (hsame_symm transportCarrier)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportEndpoint
  exact ⟨endpointUnary, classifierRow, provenancePkg⟩

end BEDC.Derived.MeasureUp
