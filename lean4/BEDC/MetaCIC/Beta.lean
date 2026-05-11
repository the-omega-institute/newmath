import BEDC.MetaCIC.Syntax

namespace BEDC.MetaCIC

/-- 朴素 substitute: 把 depth 处变量替换为 v；V1 假设 v 是 closed term。 -/
def substitute (depth : Idx) (v : Term) : Term → Term
  | Term.var i => if i = depth then v else Term.var i
  | Term.app f a => Term.app (substitute depth v f) (substitute depth v a)
  | Term.lam d b => Term.lam (substitute depth v d) (substitute (depth + 1) v b)
  | Term.pi d c => Term.pi (substitute depth v d) (substitute (depth + 1) v c)
  | Term.sort => Term.sort

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
