import BEDC.Derived.CauchyLimitSealUp.ObservationBudgetPullback

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealObservationBudgetUp

theorem CauchyLimitSealCarrier_real_observation_budget_handoff [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint budgetE
      budgetW budgetD budgetR budgetS budgetH budgetC budgetP budgetN window budgetRead
      completionRead realRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg →
      (∃ packet : RealObservationBudgetUp,
        packet = RealObservationBudgetUp.mk budgetE budgetW budgetD budgetR budgetS budgetH
          budgetC budgetP budgetN) →
        Cont schedule source window →
          Cont window dyadic budgetRead →
            Cont budgetRead diagonal completionRead →
              Cont completionRead endpoint realRead →
                hsame dyadic budgetRead →
                  hsame budgetS sealRow →
                    UnaryHistory window ∧ UnaryHistory budgetRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory realRead ∧
                        hsame sealRow completionRead ∧ hsame budgetS completionRead ∧
                          PkgSig bundle endpoint pkg ∧
                            (Cont realRead (BHist.e0 hostTail) budgetRead → False) ∧
                              (Cont realRead (BHist.e1 hostTail) budgetRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier budgetPacket scheduleSourceWindow windowDyadicBudget budgetDiagonalCompletion
    completionEndpoint sameDyadicBudget sameBudgetSeal
  have pullback :=
    CauchyLimitSealCarrier_observation_budget_pullback carrier budgetPacket
      scheduleSourceWindow windowDyadicBudget budgetDiagonalCompletion sameDyadicBudget
      sameBudgetSeal
  obtain ⟨windowUnary, budgetReadUnary, completionReadUnary, sameSealCompletion,
    sameBudgetCompletion, endpointPkg⟩ := pullback
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, _endpointPkg⟩ := carrier
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed completionReadUnary endpointUnary completionEndpoint
  have budgetCompletionReal : Cont budgetRead (append diagonal endpoint) realRead := by
    cases budgetDiagonalCompletion
    exact completionEndpoint.trans (append_assoc budgetRead diagonal endpoint)
  exact
    ⟨windowUnary, budgetReadUnary, completionReadUnary, realReadUnary, sameSealCompletion,
      sameBudgetCompletion, endpointPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left budgetCompletionReal hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right budgetCompletionReal hostReturn)⟩

end BEDC.Derived.CauchyLimitSealUp
