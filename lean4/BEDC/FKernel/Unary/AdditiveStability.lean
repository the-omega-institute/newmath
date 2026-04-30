import BEDC.FKernel.Unary.Commutativity

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem additive_stability_certificate_fields :
    (∀ {h k r : BHist}, UnaryHistory h → UnaryHistory k → Cont h k r → UnaryHistory r) ∧
      (∀ {h left right : BHist},
        UnaryHistory h → Cont h BHist.Empty left → Cont BHist.Empty h right →
          UnaryHistory left ∧ UnaryHistory right ∧ hsame left h ∧ hsame right h) ∧
      (∀ {a b c ab bc abc abc' : BHist},
        UnaryHistory a → UnaryHistory b → UnaryHistory c →
          Cont a b ab → Cont b c bc → Cont ab c abc → Cont a bc abc' →
            hsame abc abc') ∧
      (∀ {h k r r' : BHist}, Cont h k r → Cont h k r' → hsame r r') := by
  constructor
  · intro h k r uh uk hr
    exact unary_cont_closed uh uk hr
  · constructor
    · intro h left right uh hleft hright
      exact unary_cont_unit uh hleft hright
    · constructor
      · intro a b c ab bc abc abc' ua ub uc hab hbc habc habc'
        exact unary_continuation_associativity ua ub uc hab hbc habc habc'
      · intro h k r r' hr hr'
        exact cont_deterministic hr hr'

end BEDC.FKernel.Unary
