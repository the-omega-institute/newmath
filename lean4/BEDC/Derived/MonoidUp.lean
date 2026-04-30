import BEDC.FKernel.Cont

namespace BEDC.Derived.MonoidUp

def MonoidClassifierSpec {C : Type} (sameC : C → C → Prop) (x y : C) : Prop :=
  sameC x y

theorem monoid_stability_certificate_fields {C : Type} {sameC : C → C → Prop}
    {mul : C → C → C} {e : C} (reflC : ∀ x, sameC x x)
    (transC : ∀ {x y z}, sameC x y → sameC y z → sameC x z)
    (assocC : ∀ x y z, sameC (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, sameC (mul e x) x) (rightId : ∀ x, sameC (mul x e) x)
    (mulCongr : ∀ {a a' b b'}, sameC a a' → sameC b b' →
      sameC (mul a b) (mul a' b')) :
    (∀ x : C, MonoidClassifierSpec sameC x x) ∧
      (∀ {x y z : C}, MonoidClassifierSpec sameC x y →
        MonoidClassifierSpec sameC y z →
          MonoidClassifierSpec sameC x z) ∧
      (∀ x y z : C,
        MonoidClassifierSpec sameC (mul (mul x y) z) (mul x (mul y z))) ∧
      (∀ x : C, MonoidClassifierSpec sameC (mul e x) x) ∧
      (∀ x : C, MonoidClassifierSpec sameC (mul x e) x) ∧
      (∀ {a a' b b' : C}, MonoidClassifierSpec sameC a a' →
        MonoidClassifierSpec sameC b b' →
          MonoidClassifierSpec sameC (mul a b) (mul a' b')) := by
  constructor
  · intro x
    exact reflC x
  · constructor
    · intro x y z hxy hyz
      exact transC hxy hyz
    · constructor
      · intro x y z
        exact assocC x y z
      · constructor
        · intro x
          exact leftId x
        · constructor
          · intro x
            exact rightId x
          · intro a a' b b' haa' hbb'
            exact mulCongr haa' hbb'

theorem history_continuation_monoid_laws :
    (∀ h : BEDC.FKernel.Hist.BHist,
      BEDC.FKernel.Cont.Cont BEDC.FKernel.Hist.BHist.Empty h h) ∧
      (∀ h : BEDC.FKernel.Hist.BHist,
        BEDC.FKernel.Cont.Cont h BEDC.FKernel.Hist.BHist.Empty h) ∧
      (∀ {a b c ab abc bc abc' : BEDC.FKernel.Hist.BHist},
        BEDC.FKernel.Cont.Cont a b ab →
          BEDC.FKernel.Cont.Cont ab c abc →
          BEDC.FKernel.Cont.Cont b c bc →
          BEDC.FKernel.Cont.Cont a bc abc' →
          BEDC.FKernel.Hist.hsame abc abc') := by
  constructor
  · exact BEDC.FKernel.Cont.cont_left_unit
  · constructor
    · exact BEDC.FKernel.Cont.cont_right_unit
    · intro a b c ab abc bc abc' hab habc hbc habc'
      cases hab
      cases habc
      cases hbc
      cases habc'
      exact BEDC.FKernel.Cont.append_assoc a b c

end BEDC.Derived.MonoidUp
