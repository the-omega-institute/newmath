import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_ledger_exactness_obligation [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      branchRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg -> hsame branchRead branch ->
      UnaryHistory branchRead ∧ UnaryHistory branch ∧ Cont branch transport continuation ∧
        Cont output continuation provenance ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameBranchRead
  obtain ⟨_su, _lu, _wu, _ou, _outu, branchUnary, _tu, _cu, _pu, _nu, _slw, _woo,
    branchTransportContinuation, outputContinuationProvenance, _cnp, provenancePkg, _np⟩ :=
    carrier
  exact
    ⟨unary_transport branchUnary (hsame_symm sameBranchRead),
      branchUnary,
      branchTransportContinuation,
      outputContinuationProvenance,
      provenancePkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp
