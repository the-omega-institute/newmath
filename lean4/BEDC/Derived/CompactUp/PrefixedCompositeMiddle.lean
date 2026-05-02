import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactNetWitness_prefixed_composite_middle_deterministic_factorization
    {p center precision extra composite refined : BHist} :
    UnaryHistory precision -> UnaryHistory extra -> Cont precision extra composite ->
      CompactNetWitness (append p center) composite (append p refined) ->
        ∃ net : BHist, CompactNetWitness center precision net ∧
          CompactNetWitness net extra refined ∧
            (∀ {net' : BHist}, CompactNetWitness center precision net' ->
              CompactNetWitness net' extra refined -> hsame net net') := by
  intro precisionCarrier extraCarrier compositeRel prefixedWitness
  have factorized :=
    CompactNetWitness_prefixed_composite_factorizes precisionCarrier extraCarrier compositeRel
      prefixedWitness
  cases factorized with
  | intro net netData =>
      exact Exists.intro net
        (And.intro netData.left
          (And.intro netData.right
            (by
              intro net' displayedFirst _displayedSecond
              exact cont_deterministic netData.left.right.right.right
                displayedFirst.right.right.right)))

end BEDC.Derived.CompactUp
