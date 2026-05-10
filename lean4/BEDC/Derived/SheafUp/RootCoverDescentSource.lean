import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootCoverDescentSource
    (ambient member overlap route germ nextRoute nextGerm : BHist) : Prop :=
  SheafBHistCoverNerveLedger ambient member overlap route germ ∧ UnaryHistory nextRoute ∧
    Cont member nextRoute nextGerm

theorem SheafRootCoverDescentSource_rows
    {ambient member overlap route germ nextRoute nextGerm : BHist} :
    SheafRootCoverDescentSource ambient member overlap route germ nextRoute nextGerm ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ∧
        UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap ∧
          UnaryHistory nextRoute ∧ UnaryHistory nextGerm ∧
            Cont member nextRoute nextGerm := by
  intro source
  have nextGermUnary : UnaryHistory nextGerm :=
    unary_cont_closed source.left.right.left source.right.left source.right.right
  exact And.intro source.left
    (And.intro source.left.left
      (And.intro source.left.right.left
        (And.intro source.left.right.right.left
          (And.intro source.right.left
            (And.intro nextGermUnary source.right.right)))))

end BEDC.Derived.SheafUp
