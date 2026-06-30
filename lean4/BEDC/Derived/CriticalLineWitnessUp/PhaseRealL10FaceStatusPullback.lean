import BEDC.Derived.CriticalLineWitnessUp.PhaseRealRootReadbackCertificate

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPhaseRealL10FaceStatusPullback
    {Z S M R Q H C P N fixedStrip phaseReal regSeq streamName sourceBudget budgetRead
      realRead zeroStrip ratRead regSeqRead modulusRead windowRead faceStatus : BHist} :
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
                                Cont windowRead N faceStatus ->
                                  UnaryHistory fixedStrip ∧ UnaryHistory phaseReal ∧
                                    UnaryHistory regSeq ∧ UnaryHistory streamName ∧
                                      UnaryHistory sourceBudget ∧ UnaryHistory budgetRead ∧
                                        UnaryHistory realRead ∧ UnaryHistory zeroStrip ∧
                                          UnaryHistory ratRead ∧ UnaryHistory regSeqRead ∧
                                            UnaryHistory modulusRead ∧
                                              UnaryHistory windowRead ∧
                                                UnaryHistory faceStatus ∧
                                                  hsame H (append Z S) ∧
                                                    Cont windowRead N faceStatus := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet fixedStripRoute phaseRealRoute regSeqRoute streamNameRoute
    sourceBudgetRoute budgetRoute budgetReadRoute zeroStripRoute ratReadRoute realReadRoute
    regSeqReadRoute modulusReadRoute windowReadRoute faceStatusRoute
  have rootReadback :
      UnaryHistory fixedStrip ∧ UnaryHistory phaseReal ∧ UnaryHistory regSeq ∧
        UnaryHistory streamName ∧ UnaryHistory sourceBudget ∧ UnaryHistory budgetRead ∧
          UnaryHistory realRead ∧ UnaryHistory zeroStrip ∧ UnaryHistory ratRead ∧
            UnaryHistory regSeqRead ∧ UnaryHistory modulusRead ∧ UnaryHistory windowRead ∧
              hsame H (append Z S) :=
    CriticalLineWitnessPhaseRealRootReadbackCertificate packet fixedStripRoute phaseRealRoute
      regSeqRoute streamNameRoute sourceBudgetRoute budgetRoute budgetReadRoute zeroStripRoute
      ratReadRoute realReadRoute regSeqReadRoute modulusReadRoute windowReadRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain
    ⟨unaryFixedStrip, unaryPhaseReal, unaryRegSeq, unaryStreamName, unarySourceBudget,
      unaryBudgetRead, unaryRealRead, unaryZeroStrip, unaryRatRead, unaryRegSeqRead,
      unaryModulusRead, unaryWindowRead, sameH⟩ := rootReadback
  have unaryFaceStatus : UnaryHistory faceStatus :=
    unary_cont_closed unaryWindowRead routeClosure.right.right.left faceStatusRoute
  exact
    ⟨unaryFixedStrip, unaryPhaseReal, unaryRegSeq, unaryStreamName, unarySourceBudget,
      unaryBudgetRead, unaryRealRead, unaryZeroStrip, unaryRatRead, unaryRegSeqRead,
      unaryModulusRead, unaryWindowRead, unaryFaceStatus, sameH, faceStatusRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
