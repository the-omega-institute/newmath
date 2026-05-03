import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_target_descent
    {a r morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) morph ->
      (hsame morph BHist.Empty -> False) ->
        exists k : BHist, morph = BHist.e1 k /\
          CategoryHomCarrier (BHist.e1 a) r k := by
  intro homCarrier nonempty
  cases CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_cases homCarrier nonempty with
  | intro k data =>
      exact Exists.intro k
        (And.intro data.left
          (And.intro (unary_e1_closed data.right.left)
            (And.intro data.right.right.right.left
              (And.intro data.right.right.left data.right.right.right.right))))

theorem CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_descent_unique
    {a r morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) morph ->
      (hsame morph BHist.Empty -> False) ->
        exists k : BHist, morph = BHist.e1 k /\
          CategoryHomCarrier (BHist.e1 a) r k /\
            (forall {k' : BHist}, morph = BHist.e1 k' ->
              CategoryHomCarrier (BHist.e1 a) r k' -> hsame k k') := by
  intro homCarrier nonempty
  cases CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_target_descent
      homCarrier nonempty with
  | intro k data =>
      exact Exists.intro k
        (And.intro data.left
          (And.intro data.right
            (fun {k'} morphEq _descendedCarrier => by
              cases data.left
              cases morphEq
              exact hsame_refl k)))

end BEDC.Derived.CategoryUp
