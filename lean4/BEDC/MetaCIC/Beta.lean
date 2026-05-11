import BEDC.MetaCIC.Syntax

namespace BEDC.MetaCIC

/-- 单步 β-reduction。 -/
inductive BetaStep : Term → Term → Prop
  | beta (dom body arg : Term) :
      BetaStep (Term.app (Term.lam dom body) arg) (substitute 0 arg body)
  | congApp1 (f f' a : Term) :
      BetaStep f f' →
      BetaStep (Term.app f a) (Term.app f' a)
  | congApp2 (f a a' : Term) :
      BetaStep a a' →
      BetaStep (Term.app f a) (Term.app f a')
  | congLam (d b b' : Term) :
      BetaStep b b' →
      BetaStep (Term.lam d b) (Term.lam d b')

end BEDC.MetaCIC
