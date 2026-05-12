import BEDC.MetaCIC.Normalization
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.ClosurePreservation
import BEDC.MetaCIC.TypedExamples.ChurchGallery.BoolNat

namespace BEDC.MetaCIC

def evalClosedAppStep : (Term → Term) → Term → Term → Term
  | rec, Term.lam _ body, a => rec (substitute 0 a body)
  | _, Term.var i, a => Term.app (Term.var i) a
  | _, Term.app f x, a => Term.app (Term.app f x) a
  | _, Term.pi d c, a => Term.app (Term.pi d c) a
  | _, Term.sort, a => Term.app Term.sort a

def evalClosed : Nat → Term → Term
  | 0, t => t
  | _ + 1, Term.sort => Term.sort
  | _ + 1, Term.var i => Term.var i
  | n + 1, Term.lam dom body =>
      Term.lam (evalClosed n dom) (evalClosed n body)
  | n + 1, Term.pi dom cod =>
      Term.pi (evalClosed n dom) (evalClosed n cod)
  | n + 1, Term.app f a =>
      evalClosedAppStep (evalClosed n) (evalClosed n f) (evalClosed n a)

theorem evalClosedAppStep_preserves_closed (fuel : Nat) (n : Idx)
    (f' a' : Term)
    (hf : ClosedAt n f') (ha : ClosedAt n a')
    (ih : (t : Term) → ClosedAt n t → ClosedAt n (evalClosed fuel t)) :
    ClosedAt n (evalClosedAppStep (evalClosed fuel) f' a') := by
  cases f' with
  | var i =>
      unfold evalClosedAppStep
      apply ClosedAt.appClosed
      · exact hf
      · exact ha
  | app f a =>
      unfold evalClosedAppStep
      apply ClosedAt.appClosed
      · exact hf
      · exact ha
  | lam dom body =>
      unfold evalClosedAppStep
      cases hf with
      | lamClosed _ hbody =>
          exact ih (substitute 0 a' body)
            (substitute_preserves_closed_at (Nat.zero_le n) ha hbody)
  | pi dom cod =>
      unfold evalClosedAppStep
      apply ClosedAt.appClosed
      · exact hf
      · exact ha
  | sort =>
      unfold evalClosedAppStep
      apply ClosedAt.appClosed
      · exact hf
      · exact ha

theorem evalClosedAppStep_betaStar (fuel : Nat)
    (f a f' a' : Term)
    (hf : BetaStarStep f f') (ha : BetaStarStep a a')
    (ih : (t : Term) → BetaStarStep t (evalClosed fuel t)) :
    BetaStarStep (Term.app f a)
      (evalClosedAppStep (evalClosed fuel) f' a') := by
  cases f' with
  | var i =>
      unfold evalClosedAppStep
      exact betaStarStep_app_double hf ha
  | app ff aa =>
      unfold evalClosedAppStep
      exact betaStarStep_app_double hf ha
  | lam dom body =>
      unfold evalClosedAppStep
      exact
        betaStar_trans
          (betaStarStep_app_double hf ha)
          (betaStar_trans
            (betaStar_one (BetaStep.beta dom body a'))
            (ih (substitute 0 a' body)))
  | pi dom cod =>
      unfold evalClosedAppStep
      exact betaStarStep_app_double hf ha
  | sort =>
      unfold evalClosedAppStep
      exact betaStarStep_app_double hf ha

theorem evalClosed_preserves_closed_at (fuel : Nat) (n : Idx) (t : Term)
    (h : ClosedAt n t) :
    ClosedAt n (evalClosed fuel t) := by
  induction fuel generalizing n t with
  | zero =>
      exact h
  | succ fuel ih =>
      cases t with
      | var i =>
          exact h
      | app f a =>
          cases h with
          | appClosed hf ha =>
              unfold evalClosed
              exact evalClosedAppStep_preserves_closed fuel n
                (evalClosed fuel f) (evalClosed fuel a)
                (ih n f hf)
                (ih n a ha)
                (ih n)
      | lam dom body =>
          cases h with
          | lamClosed hdom hbody =>
              unfold evalClosed
              apply ClosedAt.lamClosed
              · exact ih n dom hdom
              · exact ih (n + 1) body hbody
      | pi dom cod =>
          cases h with
          | piClosed hdom hcod =>
              unfold evalClosed
              apply ClosedAt.piClosed
              · exact ih n dom hdom
              · exact ih (n + 1) cod hcod
      | sort =>
          exact ClosedAt.sortClosed

theorem evalClosed_preserves_closed (fuel : Nat) (t : Term)
    (h : ClosedAt 0 t) :
    ClosedAt 0 (evalClosed fuel t) := by
  exact evalClosed_preserves_closed_at fuel 0 t h

theorem evalClosed_betaStar_any (fuel : Nat) (t : Term) :
    BetaStarStep t (evalClosed fuel t) := by
  induction fuel generalizing t with
  | zero =>
      exact BetaStarStep.refl t
  | succ fuel ih =>
      cases t with
      | var i =>
          exact BetaStarStep.refl (Term.var i)
      | app f a =>
          unfold evalClosed
          exact evalClosedAppStep_betaStar fuel f a
            (evalClosed fuel f) (evalClosed fuel a)
            (ih f) (ih a) ih
      | lam dom body =>
          unfold evalClosed
          exact betaStarStep_lam_double (ih dom) (ih body)
      | pi dom cod =>
          unfold evalClosed
          exact betaStarStep_pi_double (ih dom) (ih cod)
      | sort =>
          exact BetaStarStep.refl Term.sort

theorem evalClosed_betaStar (fuel : Nat) (t : Term)
    (_h : ClosedAt 0 t) :
    BetaStarStep t (evalClosed fuel t) := by
  exact evalClosed_betaStar_any fuel t

example :
    evalClosed 10
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort) =
    Term.sort := by
  rfl

example :
    evalClosed 20
      (Term.app (Term.app (Term.app churchZeroTm Term.sort) Term.sort) Term.sort) =
    Term.sort := by
  rfl

end BEDC.MetaCIC
