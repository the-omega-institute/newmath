import BEDC.Derived.SheafUp
import BEDC.Derived.SheafUp.ChartGluingTrace
import BEDC.Derived.SheafUp.ConsumerAccessTraceSource
import BEDC.Derived.SheafUp.ConsumerAccessTrace

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootAccessNormalFormSourceCase (root : BHist) : Prop :=
  (exists sectionHist classifier : BHist,
    UnaryHistory root ∧ UnaryHistory sectionHist ∧ hsame sectionHist classifier) ∨
  (exists openHist sectionHist result : BHist,
    UnaryHistory root ∧ UnaryHistory openHist ∧ Cont openHist sectionHist result) ∨
  (exists member cover : BHist,
    UnaryHistory root ∧ UnaryHistory member ∧ hsame member cover) ∨
  (exists common sectA sectB germA germB : BHist,
    UnaryHistory root ∧ UnaryHistory common ∧ Cont common sectA germA ∧
      Cont common sectB germB ∧ hsame germA germB)

theorem SheafSchemeChartGluingTrace_consumer_access_trace
    {point common : BHist} {sections : List BHist} {out : BHist} :
    SheafSchemeChartGluingTrace point common sections out ->
      SheafConsumerAccessTrace common sections ∧ UnaryHistory out := by
  intro trace
  induction trace with
  | nil _ commonUnary =>
      exact And.intro
        (And.intro commonUnary
          (by
            intro row rowMem
            cases rowMem))
        unary_empty
  | cons commonUnary sectionUnary commonSection _tailTrace germTail tailRows =>
      have germUnary : UnaryHistory _ :=
        unary_cont_closed commonUnary sectionUnary commonSection
      have outUnary : UnaryHistory _ :=
        unary_cont_closed germUnary tailRows.right germTail
      exact And.intro
        (And.intro commonUnary
          (by
            intro row rowMem
            cases rowMem with
            | head =>
                exact sectionUnary
            | tail _ tailMem =>
                exact tailRows.left.right row tailMem))
        outUnary

theorem SheafRootAccessNormalForm_source_cases {root : BHist} :
    SheafConsumerAccessTraceSource root -> SheafRootAccessNormalFormSourceCase root := by
  intro source
  cases source with
  | carrierClassifier rootUnary sectionUnary sameSection =>
      exact Or.inl
        (Exists.intro _
          (Exists.intro _
            (And.intro rootUnary (And.intro sectionUnary sameSection))))
  | restrictionRoute rootUnary openUnary route =>
      exact Or.inr
        (Or.inl
          (Exists.intro _
            (Exists.intro _
              (Exists.intro _
                (And.intro rootUnary (And.intro openUnary route))))))
  | coverMembership rootUnary memberUnary sameMember =>
      exact Or.inr
        (Or.inr
          (Or.inl
            (Exists.intro _
              (Exists.intro _
                (And.intro rootUnary (And.intro memberUnary sameMember))))))
  | localityGluing rootUnary commonUnary leftRoute rightRoute sameGerms =>
      exact Or.inr
        (Or.inr
          (Or.inr
            (Exists.intro _
              (Exists.intro _
                (Exists.intro _
                  (Exists.intro _
                    (Exists.intro _
                      (And.intro rootUnary
                        (And.intro commonUnary
                          (And.intro leftRoute (And.intro rightRoute sameGerms)))))))))))

theorem SheafRootAccessNormalForm_consumer_factorization
    {root h k : BHist} {landing : SheafRootFaceLanding} {trace : List BHist} :
    SheafConsumerAccessTrace root trace -> List.Mem h trace ->
      SheafRootFaceRead h k landing ->
        UnaryHistory root ∧ UnaryHistory h ∧
          ((landing = SheafRootFaceLanding.coverMembership ∧ hsame h k) ∨
            (landing = SheafRootFaceLanding.restrictionRoute ∧
              (hsame h k ∨ ∃ sectionHist : BHist, Cont h sectionHist k)) ∨
              (landing = SheafRootFaceLanding.localityGluingRefinement ∧
                ∃ sectA : BHist, ∃ sectB : BHist, ∃ germB : BHist,
                  Cont h sectA k ∧ Cont h sectB germB ∧ hsame k germB)) := by
  intro consumer hMem read
  have hUnary : UnaryHistory h :=
    consumer.right h hMem
  cases read with
  | carrierClassifier sameHK =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inr
            (Or.inl
              (And.intro rfl (Or.inl sameHK)))))
  | restrictionRoute route =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inr
            (Or.inl
              (And.intro rfl (Or.inr (Exists.intro _ route))))))
  | coverMembership sameHK =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inl (And.intro rfl sameHK)))
  | localityGluingRefinement routeA routeB sameGerms =>
      exact And.intro consumer.left
        (And.intro hUnary
          (Or.inr
            (Or.inr
              (And.intro rfl
                (Exists.intro _
                  (Exists.intro _
                    (Exists.intro _
                      (And.intro routeA (And.intro routeB sameGerms)))))))))

end BEDC.Derived.SheafUp
