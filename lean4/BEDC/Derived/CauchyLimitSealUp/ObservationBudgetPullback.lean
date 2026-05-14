import BEDC.Derived.CauchyLimitSealUp
import BEDC.Derived.RealObservationBudgetUp.TasteGate

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealObservationBudgetUp

theorem CauchyLimitSealCarrier_observation_budget_pullback [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint budgetE budgetW
      budgetD budgetR budgetS budgetH budgetC budgetP budgetN window budgetRead completionRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg →
      (∃ packet : RealObservationBudgetUp,
        packet = RealObservationBudgetUp.mk budgetE budgetW budgetD budgetR budgetS budgetH
          budgetC budgetP budgetN) →
        Cont schedule source window →
          Cont window dyadic budgetRead →
            Cont budgetRead diagonal completionRead →
              hsame dyadic budgetRead →
                hsame budgetS sealRow →
                  UnaryHistory window ∧ UnaryHistory budgetRead ∧ UnaryHistory completionRead ∧
                    hsame sealRow completionRead ∧ hsame budgetS completionRead ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier budgetPacket scheduleSourceWindow windowDyadicBudget budgetDiagonalCompletion
    sameDyadicBudget sameBudgetSeal
  obtain ⟨_packet, packetEq⟩ := budgetPacket
  cases packetEq
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicBudget
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetReadUnary diagonalUnary budgetDiagonalCompletion
  have sameSealCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicBudget (hsame_refl diagonal) dyadicDiagonalSeal
      budgetDiagonalCompletion
  have sameBudgetCompletion : hsame budgetS completionRead :=
    hsame_trans sameBudgetSeal sameSealCompletion
  exact
    ⟨windowUnary, budgetReadUnary, completionReadUnary, sameSealCompletion,
      sameBudgetCompletion, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp
