import BEDC.Derived.FiniteCauchyGluingBudgetUp.SynchronizerWindowExactness

namespace BEDC.Derived.FiniteCauchyGluingBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def FiniteCauchyGluingBudgetClassifier
    (G L T S K U D V R H C P N G' L' T' S' K' U' D' V' R' H' C' P' N' : BHist) :
    Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  hsame G G' ∧ hsame L L' ∧ hsame T T' ∧ hsame S S' ∧ hsame K K' ∧
    hsame U U' ∧ hsame D D' ∧ hsame V V' ∧ hsame R R' ∧ hsame H H' ∧
      hsame C C' ∧ hsame P P' ∧ hsame N N'

theorem FiniteCauchyGluingBudgetClassifier_synchronizer_window
    {G L T S K U D V R H C P N G' L' T' S' K' U' D' V' R' H' C' P' N'
      tailRead tailRead' : BHist} :
    FiniteCauchyGluingBudgetClassifier G L T S K U D V R H C P N
        G' L' T' S' K' U' D' V' R' H' C' P' N' →
      Cont T S tailRead →
        Cont T' S' tailRead' →
          hsame tailRead tailRead' ∧ hsame S S' ∧ hsame K K' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro classifier leftRoute rightRoute
  exact
    ⟨cont_respects_hsame classifier.right.right.left classifier.right.right.right.left leftRoute
        rightRoute,
      classifier.right.right.right.left,
      classifier.right.right.right.right.left⟩

end BEDC.Derived.FiniteCauchyGluingBudgetUp
