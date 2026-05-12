import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

/-- A generator-closure classifier on a carrier type `α`:
    a unary predicate `Classifier` together with a binary relation `Generator`
    such that the classifier is closed under the generator. -/
structure GeneratorClosureClassifier (α : Type u)
    (Generator : α → α → Prop) (Classifier : α → Prop) : Prop where
  closure : ∀ {x y : α}, Generator x y → Classifier x → Classifier y

def closed_under_shift_classifier (n : Idx) :
    GeneratorClosureClassifier Term
      (fun t1 t2 => t2 = shift n 1 t1)
      (ClosedAt n) :=
  { closure := by
      intro x y hgen hclosed
      rw [hgen, shift_closed n x hclosed]
      exact hclosed }

def closed_under_substitute_classifier (d : Idx) :
    GeneratorClosureClassifier Term
      (fun t1 t2 => ∃ v, t2 = substitute d v t1)
      (ClosedAt d) :=
  { closure := by
      intro x y hgen hclosed
      cases hgen with
      | intro v hv =>
          rw [hv, substitute_closed d v x hclosed]
          exact hclosed }

end BEDC.MetaCIC
