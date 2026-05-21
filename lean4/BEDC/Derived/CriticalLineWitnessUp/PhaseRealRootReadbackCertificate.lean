import BEDC.Derived.CriticalLineWitnessUp.PhaseRealSourceBudgetReadiness
import BEDC.Derived.CriticalLineWitnessUp.PhaseRealSourceTriad
import BEDC.Derived.CriticalLineWitnessUp.PhaseRealSourceWindowExhaustion

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPhaseRealRootReadbackCertificate
    {Z S M R Q H C P N fixedStrip phaseReal regSeq streamName sourceBudget budgetRead
      zeroStrip ratRead realRead regSeqRead modulusRead windowRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S fixedStrip ->
        Cont fixedStrip M phaseReal ->
          Cont phaseReal R regSeq ->
            Cont regSeq Q streamName ->
              Cont S M sourceBudget ->
                Cont sourceBudget R budgetRead ->
                  Cont budgetRead Q realRead ->
                    Cont Z S zeroStrip ->
                      Cont M R ratRead ->
                        Cont ratRead Q realRead ->
                          Cont realRead H regSeqRead ->
                            Cont regSeqRead C modulusRead ->
                              Cont modulusRead P windowRead ->
                                UnaryHistory fixedStrip ∧ UnaryHistory phaseReal ∧
                                  UnaryHistory regSeq ∧ UnaryHistory streamName ∧
                                    UnaryHistory sourceBudget ∧ UnaryHistory budgetRead ∧
                                      UnaryHistory realRead ∧ UnaryHistory zeroStrip ∧
                                        UnaryHistory ratRead ∧ UnaryHistory regSeqRead ∧
                                          UnaryHistory modulusRead ∧
                                            UnaryHistory windowRead ∧
                                              hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet fixedStripRoute phaseRealRoute regSeqRoute streamNameRoute
    sourceBudgetRoute budgetRoute budgetReadRoute zeroStripRoute ratReadRoute realReadRoute
    regSeqReadRoute modulusReadRoute windowReadRoute
  have triad :=
    CriticalLineWitnessPhaseRealSourceTriad packet fixedStripRoute phaseRealRoute
      regSeqRoute streamNameRoute
  have budget :=
    CriticalLineWitnessPhaseRealSourceBudgetReadiness packet sourceBudgetRoute budgetRoute
      budgetReadRoute
  have window :=
    CriticalLineWitnessPhaseRealSourceWindowExhaustion packet zeroStripRoute ratReadRoute
      realReadRoute regSeqReadRoute modulusReadRoute windowReadRoute
  obtain
    ⟨_unaryZTriad, _unarySTriad, _unaryMTriad, _unaryRTriad, _unaryQTriad,
      unaryFixedStrip, unaryPhaseReal, unaryRegSeq, unaryStreamName, sameH, _fixedRoute,
      _phaseRoute, _regSeqRoute, _streamRoute⟩ := triad
  obtain
    ⟨_unaryZBudget, _unarySBudget, _unaryMBudget, _unaryRBudget, _unaryQBudget,
      unarySourceBudget, unaryBudgetRead, unaryRealReadFromBudget, _sameHBudget,
      _sourceBudgetRoute, _budgetRoute, _budgetReadRoute, _routeCFromBudget,
      _routeNFromBudget⟩ := budget
  obtain
    ⟨_unaryZWindow, _unarySWindow, _unaryMWindow, _unaryRWindow, _unaryQWindow,
      unaryZeroStrip, unaryRatRead, _unaryRealReadFromWindow, unaryRegSeqRead,
      unaryModulusRead, unaryWindowRead, _sameHWindow, _zeroStripRoute, _ratReadRoute,
      _realReadRoute, _regSeqReadRoute, _modulusReadRoute, _windowReadRoute⟩ := window
  exact
    ⟨unaryFixedStrip, unaryPhaseReal, unaryRegSeq, unaryStreamName, unarySourceBudget,
      unaryBudgetRead, unaryRealReadFromBudget, unaryZeroStrip, unaryRatRead, unaryRegSeqRead,
      unaryModulusRead, unaryWindowRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
