import BEDC.MetaCIC.Confluence.AtomShape

namespace BEDC.MetaCIC

theorem betaStarStep_diamond_sort {t1 t2 : Term}
    (h1 : BetaStarStep Term.sort t1)
    (h2 : BetaStarStep Term.sort t2) :
    Exists (fun v => BetaStarStep t1 v ∧ BetaStarStep t2 v) := by
  exact betaStar_sort_join h1 h2

theorem betaStarStep_diamond_var {i : Idx} {t1 t2 : Term}
    (h1 : BetaStarStep (Term.var i) t1)
    (h2 : BetaStarStep (Term.var i) t2) :
    Exists (fun v => BetaStarStep t1 v ∧ BetaStarStep t2 v) := by
  exact betaStar_var_join i h1 h2

end BEDC.MetaCIC
