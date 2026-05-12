import BEDC.MetaCIC.Decidable.CheckClosedAtom
import BEDC.MetaCIC.Normalization
import BEDC.MetaCIC.Beta.Conversion
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.TypedExamples.ChurchGallery

namespace BEDC.MetaCIC

def contractNormalizedApp : (Term → Term) → Term → Term → Term
  | rec, Term.lam _ b, a => rec (substitute 0 a b)
  | _, Term.var i, a => Term.app (Term.var i) a
  | _, Term.app f x, a => Term.app (Term.app f x) a
  | _, Term.pi d c, a => Term.app (Term.pi d c) a
  | _, Term.sort, a => Term.app Term.sort a

def normalizeBounded : Nat → Term → Term
  | 0, t => t
  | _ + 1, Term.var i => Term.var i
  | _ + 1, Term.sort => Term.sort
  | n + 1, Term.lam d b =>
      Term.lam (normalizeBounded n d) (normalizeBounded n b)
  | n + 1, Term.pi d c =>
      Term.pi (normalizeBounded n d) (normalizeBounded n c)
  | n + 1, Term.app f a =>
      contractNormalizedApp
        (normalizeBounded n)
        (normalizeBounded n f)
        (normalizeBounded n a)

def decideClosedBetaConv (fuel : Nat) (t u : Term) : Bool :=
  Term.eq (normalizeBounded fuel t) (normalizeBounded fuel u)

def NormalizedBy (fuel : Nat) (t nf : Term) : Prop :=
  normalizeBounded fuel t = nf

def ClosedNormalForm (nf : Term) : Prop :=
  ClosedAt 0 nf ∧ BetaNormal nf

def ClosedFinishedNormalizes (fuel : Nat) (t nf : Term) : Prop :=
  ClosedAt 0 t ∧ NormalizedBy fuel t nf ∧ ClosedNormalForm nf

theorem normalizeBounded_zero (t : Term) :
    normalizeBounded 0 t = t := by
  rfl

theorem normalizeBounded_sort (fuel : Nat) :
    normalizeBounded fuel Term.sort = Term.sort := by
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      rfl

theorem normalizeBounded_var (fuel : Nat) (i : Idx) :
    normalizeBounded fuel (Term.var i) = Term.var i := by
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      rfl

theorem normalizeBounded_lam_succ (fuel : Nat) (d b : Term) :
    normalizeBounded (fuel + 1) (Term.lam d b) =
      Term.lam (normalizeBounded fuel d) (normalizeBounded fuel b) := by
  rfl

theorem normalizeBounded_pi_succ (fuel : Nat) (d c : Term) :
    normalizeBounded (fuel + 1) (Term.pi d c) =
      Term.pi (normalizeBounded fuel d) (normalizeBounded fuel c) := by
  rfl

theorem normalizeBounded_app_succ (fuel : Nat) (f a : Term) :
    normalizeBounded (fuel + 1) (Term.app f a) =
      contractNormalizedApp
        (normalizeBounded fuel)
        (normalizeBounded fuel f)
        (normalizeBounded fuel a) := by
  rfl

theorem decideClosedBetaConv_refl (fuel : Nat) (t : Term) :
    decideClosedBetaConv fuel t t = true := by
  unfold decideClosedBetaConv
  exact Term.eq_refl (normalizeBounded fuel t)

theorem decideClosedBetaConv_true_eq_normalized {fuel : Nat} {t u : Term} :
    decideClosedBetaConv fuel t u = true →
      normalizeBounded fuel t = normalizeBounded fuel u := by
  intro h
  unfold decideClosedBetaConv at h
  exact Term.eq_true_to_eq
    (normalizeBounded fuel t)
    (normalizeBounded fuel u)
    h

theorem decideClosedBetaConv_true_betaConv_normalized
    {fuel : Nat} {t u : Term} :
    decideClosedBetaConv fuel t u = true →
      BetaConv (normalizeBounded fuel t) (normalizeBounded fuel u) := by
  intro h
  have heq :
      normalizeBounded fuel t = normalizeBounded fuel u :=
    decideClosedBetaConv_true_eq_normalized h
  rw [heq]
  exact BetaConv.refl (normalizeBounded fuel u)

theorem decideClosedBetaConv_sound_finished
    {fuel : Nat} {t u nt nu : Term}
    (ht : ClosedFinishedNormalizes fuel t nt)
    (hu : ClosedFinishedNormalizes fuel u nu)
    (h : decideClosedBetaConv fuel t u = true) :
    nt = nu ∧ BetaConv nt nu ∧ ClosedNormalForm nt ∧ ClosedNormalForm nu := by
  cases ht with
  | intro _ htRest =>
      cases htRest with
      | intro htNorm htNF =>
          cases hu with
          | intro _ huRest =>
              cases huRest with
              | intro huNorm huNF =>
                  have hnormEq :
                      normalizeBounded fuel t = normalizeBounded fuel u :=
                    decideClosedBetaConv_true_eq_normalized h
                  rw [htNorm] at hnormEq
                  rw [huNorm] at hnormEq
                  cases hnormEq
                  exact
                    And.intro rfl
                      (And.intro
                        (BetaConv.refl nt)
                        (And.intro htNF htNF))

theorem decideClosedBetaConv_sound_finished_betaConv
    {fuel : Nat} {t u nt nu : Term}
    (ht : ClosedFinishedNormalizes fuel t nt)
    (hu : ClosedFinishedNormalizes fuel u nu)
    (h : decideClosedBetaConv fuel t u = true) :
    BetaConv nt nu := by
  exact (decideClosedBetaConv_sound_finished ht hu h).right.left

theorem decideClosedBetaConv_sound_finished_eq
    {fuel : Nat} {t u nt nu : Term}
    (ht : ClosedFinishedNormalizes fuel t nt)
    (hu : ClosedFinishedNormalizes fuel u nu)
    (h : decideClosedBetaConv fuel t u = true) :
    nt = nu := by
  exact (decideClosedBetaConv_sound_finished ht hu h).left

example : decideClosedBetaConv 1 churchTrueTm churchTrueTm = true := by
  rfl

example : decideClosedBetaConv 1 churchTrueTm churchFalseTm = false := by
  rfl

example :
    decideClosedBetaConv 1
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      Term.sort = true := by
  rfl

example :
    decideClosedBetaConv 1
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      churchTrueTm = false := by
  rfl

end BEDC.MetaCIC
