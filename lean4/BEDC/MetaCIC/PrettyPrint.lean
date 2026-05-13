import BEDC.MetaCIC.Syntax

namespace BEDC.MetaCIC

/-- Render a MetaCIC Term as a human-readable string with explicit
    de Bruijn indices and binder forms. Pure structural recursion;
    no host coupling. -/
def pp : Term → String
  | Term.var i => "v" ++ toString i
  | Term.app f a => "(" ++ pp f ++ " " ++ pp a ++ ")"
  | Term.lam d b => "(λ:" ++ pp d ++ " . " ++ pp b ++ ")"
  | Term.pi d c => "(Π:" ++ pp d ++ " . " ++ pp c ++ ")"
  | Term.sort => "Sort"

example : pp Term.sort = "Sort" := rfl

example : pp (Term.var 0) = "v0" := rfl

example : pp (Term.lam Term.sort (Term.var 0)) = "(λ:Sort . v0)" := rfl

end BEDC.MetaCIC
