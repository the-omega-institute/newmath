import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_nonempty_morphism_target_carrier_unique
    {a target morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) target morph ->
      (hsame morph BHist.Empty -> False) ->
        exists k r : BHist, morph = BHist.e1 k ∧ target = BHist.e1 r ∧
          CategoryHomCarrier (BHist.e1 a) r k ∧
          (forall {k' r' : BHist}, morph = BHist.e1 k' -> target = BHist.e1 r' ->
            CategoryHomCarrier (BHist.e1 a) r' k' -> hsame k k' ∧ hsame r r') := by
  intro homCarrier nonempty
  cases CategoryHomCarrier_e1_source_nonempty_morphism_target_cases homCarrier nonempty with
  | intro k witness =>
      cases witness with
      | intro r data =>
          exact ⟨k, r, data.left, data.right.left,
            ⟨unary_e1_closed data.right.right.left, data.right.right.right.right.left,
              data.right.right.right.left, data.right.right.right.right.right⟩,
            fun {k'} {r'} morphEq targetEq _descended =>
              ⟨BHist.e1.inj ((Eq.symm data.left).trans morphEq),
                BHist.e1.inj ((Eq.symm data.right.left).trans targetEq)⟩⟩

theorem CategoryHomCarrier_e1_target_nonempty_morphism_source_carrier_unique
    {source r morph : BHist} :
    CategoryHomCarrier source (BHist.e1 r) morph ->
      (hsame morph BHist.Empty -> False) ->
        (source = BHist.Empty ∧ morph = BHist.e1 r ∧ UnaryHistory r ∧
          (forall {m' : BHist}, morph = BHist.e1 m' -> hsame r m')) ∨
        (exists a k : BHist, source = BHist.e1 a ∧ morph = BHist.e1 k ∧
          CategoryHomCarrier (BHist.e1 a) r k ∧
          (forall {a' k' : BHist}, source = BHist.e1 a' -> morph = BHist.e1 k' ->
            CategoryHomCarrier (BHist.e1 a') r k' -> hsame a a' ∧ hsame k k')) := by
  intro homCarrier nonempty
  cases CategoryHomCarrier_e1_target_nonempty_morphism_source_cases homCarrier nonempty with
  | inl emptySource =>
      exact Or.inl
        ⟨emptySource.left, emptySource.right.left, emptySource.right.right,
          fun {m'} morphEq => BHist.e1.inj ((Eq.symm emptySource.right.left).trans morphEq)⟩
  | inr visibleSource =>
      cases visibleSource with
      | intro a witness =>
          cases witness with
          | intro k data =>
              exact Or.inr
                ⟨a, k, data.left, data.right.left,
                  ⟨unary_e1_closed data.right.right.left, data.right.right.right.right.left,
                    data.right.right.right.left, data.right.right.right.right.right⟩,
                  fun {a'} {k'} sourceEq morphEq _descended =>
                    ⟨BHist.e1.inj ((Eq.symm data.left).trans sourceEq),
                      BHist.e1.inj ((Eq.symm data.right.left).trans morphEq)⟩⟩

end BEDC.Derived.CategoryUp
