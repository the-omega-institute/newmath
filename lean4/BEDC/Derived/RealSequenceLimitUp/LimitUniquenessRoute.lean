import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitLimitUniquenessRoute [AskSetup] [PackageSetup]
    {sequenceRow limitRow limitRow' windowSchedule windowSchedule' dyadicLedger
      dyadicLedger' classifierRow classifierRow' transportRow transportRow' continuationRow
      continuationRow' provenanceRow provenanceRow' nameRow nameRow' comparisonRead
      regularBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transportRow continuationRow provenanceRow nameRow bundle pkg ->
      RealSequenceLimitCarrier sequenceRow limitRow' windowSchedule' dyadicLedger'
          classifierRow' transportRow' continuationRow' provenanceRow' nameRow' bundle pkg ->
        Cont windowSchedule windowSchedule' comparisonRead ->
          Cont comparisonRead regularBoundary limitRow ->
            hsame regularBoundary limitRow' ->
              UnaryHistory comparisonRead ∧ UnaryHistory regularBoundary ∧
                Cont windowSchedule windowSchedule' comparisonRead ∧
                  Cont comparisonRead regularBoundary limitRow ∧ hsame regularBoundary limitRow' ∧
                    PkgSig bundle nameRow pkg ∧ PkgSig bundle nameRow' pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro leftCarrier rightCarrier scheduleComparison boundaryRoute boundarySame
  obtain ⟨_sequenceUnary, limitUnary, windowUnary, _dyadicUnary, _classifierUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary, _routeCont,
      _classifierCont, _transportSame, _routeSame, _provenancePkg, namePkg⟩ := leftCarrier
  obtain ⟨_sequenceUnary', limitUnary', windowUnary', _dyadicUnary', _classifierUnary',
    _transportUnary', _continuationUnary', _provenanceUnary', _nameUnary',
      _routeCont', _classifierCont', _transportSame', _routeSame', _provenancePkg',
        namePkg'⟩ := rightCarrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed windowUnary windowUnary' scheduleComparison
  have boundaryUnary : UnaryHistory regularBoundary :=
    unary_transport_symm limitUnary' boundarySame
  exact
    ⟨comparisonUnary, boundaryUnary, scheduleComparison, boundaryRoute, boundarySame, namePkg,
      namePkg'⟩

end BEDC.Derived.RealSequenceLimitUp
