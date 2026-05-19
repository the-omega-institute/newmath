import BEDC.Derived.CauchyCompletionFunctorUp

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionFunctorPacket_tail_budget_coherence_factorization
    [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint tailRead
      budgetRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg →
      Cont metric regular tailRead →
        Cont tailRead transport budgetRead →
          Cont budgetRead endpoint exported →
            PkgSig bundle exported pkg →
              UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory tailRead ∧
                UnaryHistory budgetRead ∧ UnaryHistory exported ∧
                  Cont metric regular tailRead ∧ Cont tailRead transport budgetRead ∧
                    Cont budgetRead endpoint exported ∧ Cont metric regular sealRow ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet metricRegularTail tailTransportBudget budgetEndpointExport exportedPkg
  obtain ⟨metricUnary, regularUnary, _sealUnary, _monadUnary, _universalUnary,
    _classifierUnary, transportUnary, _nameCertUnary, endpointUnary, metricRegularSeal,
    _monadUniversalEndpoint, _classifierTransportNameCert, endpointPkg⟩ :=
    packet
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed metricUnary regularUnary metricRegularTail
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailUnary transportUnary tailTransportBudget
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed budgetUnary endpointUnary budgetEndpointExport
  exact
    ⟨metricUnary, regularUnary, tailUnary, budgetUnary, exportedUnary, metricRegularTail,
      tailTransportBudget, budgetEndpointExport, metricRegularSeal, endpointPkg, exportedPkg⟩

end BEDC.Derived.CauchyCompletionFunctorUp
