import BEDC.Derived.FieldUp.ConcreteOperationTableLaws

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RatupFieldupAlgebraHierarchyExitWitness :
    FieldCertificateObligations
        (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
        (BHist.e1 BHist.Empty)
        (BHist.e1 BHist.Empty)
        (append BHist.Empty BHist.Empty)
        BHist.Empty
        BHist.Empty
        BHist.Empty
        BHist.Empty
        (append BHist.Empty BHist.Empty)
        BHist.Empty
        (append (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
          (append BHist.Empty BHist.Empty)) ∧
      RatupFieldupConcreteExitObject
        (BHist.e1 BHist.Empty)
        BHist.Empty
        (BHist.e1 BHist.Empty)
        BHist.Empty
        BHist.Empty
        (BHist.e1 BHist.Empty)
        (BHist.e1 BHist.Empty) ∧
      hsame (append BHist.Empty BHist.Empty) BHist.Empty := by
  -- BEDC touchpoint anchor: BHist hsame append
  exact
    ⟨RatupFieldupConcreteOperationTableLaws.left,
      RatupFieldupConcreteOperationTableLaws.right,
      hsame_refl BHist.Empty⟩

end BEDC.Derived.FieldUp
