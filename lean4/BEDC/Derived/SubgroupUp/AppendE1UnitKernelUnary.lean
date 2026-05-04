import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem SubgroupCentralizerQuotientKernel_append_e1_unit_kernel_unary
    {inv : BHist -> BHist} {x y : BHist} :
    SubgroupCentralizerQuotientKernel append inv (BHist.e1 BHist.Empty) x y ->
      UnaryHistory (append (inv x) y) := by
  intro kernel
  have centralizerUnitUnary :
      forall word : BHist,
        hsame (append word (BHist.e1 BHist.Empty))
          (append (BHist.e1 BHist.Empty) word) ->
          UnaryHistory word := by
    intro word
    induction word with
    | Empty =>
        intro _central
        exact unary_empty
    | e0 word ih =>
        intro central
        cases central
    | e1 word ih =>
        intro central
        have tailCentral :
            hsame (append word (BHist.e1 BHist.Empty))
              (append (BHist.e1 BHist.Empty) word) :=
          BHist.e1.inj central
        exact ih tailCentral
  exact centralizerUnitUnary (append (inv x) y) kernel.right.right

end BEDC.Derived.SubgroupUp
