import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem SubgroupCentralizerCarrier_append_e1_unit_unary {word : BHist} :
    SubgroupCentralizerCarrier append (BHist.e1 BHist.Empty) word -> UnaryHistory word := by
  intro central
  induction word with
  | Empty =>
      exact unary_empty
  | e0 word ih =>
      cases central
  | e1 word ih =>
      have tailCentral :
          hsame (append word (BHist.e1 BHist.Empty))
            (append (BHist.e1 BHist.Empty) word) :=
        BHist.e1.inj central
      exact ih tailCentral

theorem SubgroupCentralizerQuotientKernel_append_e1_unit_kernel_unary
    {inv : BHist -> BHist} {x y : BHist} :
    SubgroupCentralizerQuotientKernel append inv (BHist.e1 BHist.Empty) x y ->
      UnaryHistory (append (inv x) y) := by
  intro kernel
  exact SubgroupCentralizerCarrier_append_e1_unit_unary kernel.right.right

end BEDC.Derived.SubgroupUp
