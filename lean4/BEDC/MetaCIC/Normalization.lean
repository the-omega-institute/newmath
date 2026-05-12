import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Normalization.PiAdequacy

namespace BEDC.MetaCIC

theorem sort_no_beta {t : Term} : ¬ BetaStep Term.sort t := by
  intro h
  cases h

theorem closed_var_no_beta {i : Idx} {t : Term} : ¬ BetaStep (Term.var i) t := by
  intro h
  cases h

theorem betaStep_from_atom_no_target {t t' : Term}
    (h : t = Term.sort ∨ ∃ i, t = Term.var i)
    (hbeta : BetaStep t t') : False := by
  cases h with
  | inl hsort =>
      rw [hsort] at hbeta
      exact sort_no_beta hbeta
  | inr hvar =>
      cases hvar with
      | intro i hi =>
          rw [hi] at hbeta
          exact closed_var_no_beta hbeta

theorem betaStep_source_composite {t t' : Term}
    (hbeta : BetaStep t t') :
    (∃ f a, t = Term.app f a) ∨
    (∃ d b, t = Term.lam d b) ∨
    ∃ d c, t = Term.pi d c := by
  cases hbeta with
  | beta d body arg =>
      exact
        Or.inl
          (Exists.intro (Term.lam d body)
            (Exists.intro arg rfl))
  | congApp1 f f' a hff' =>
      exact
        Or.inl
          (Exists.intro f
            (Exists.intro a rfl))
  | congApp2 f a a' haa' =>
      exact
        Or.inl
          (Exists.intro f
            (Exists.intro a rfl))
  | congLam d b b' hbb' =>
      exact
        Or.inr
          (Or.inl
            (Exists.intro d
              (Exists.intro b rfl)))
  | congPiCod d c c' hcc' =>
      exact
        Or.inr
          (Or.inr
            (Exists.intro d
              (Exists.intro c rfl)))
  | congPiDom d d' c hdd' =>
      exact
        Or.inr
          (Or.inr
            (Exists.intro d
              (Exists.intro c rfl)))
  | congLamDom d d' b hdd' =>
      exact
        Or.inr
          (Or.inl
            (Exists.intro d
              (Exists.intro b rfl)))

theorem closed_atom_normal_form {Γ : Ctx} {t : Term}
    (_hclosed : ClosedAt 0 t)
    (_ht : HasType Γ t Term.sort)
    (h_atom : t = Term.sort ∨ ∃ i, t = Term.var i)
    : ¬ ∃ t', BetaStep t t' := by
  intro hstep
  cases hstep with
  | intro t' hbeta =>
      cases h_atom with
      | inl hsort =>
          rw [hsort] at hbeta
          exact sort_no_beta hbeta
      | inr hvar =>
          cases hvar with
          | intro i hi =>
              rw [hi] at hbeta
              exact closed_var_no_beta hbeta

end BEDC.MetaCIC
