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

def GeneratorClosureClassifier.refl {α : Type u}
    (Classifier : α → Prop) :
    GeneratorClosureClassifier α (fun x y => x = y) Classifier :=
  { closure := by
      intro x y hgen hclass
      cases hgen
      exact hclass }

def GeneratorClosureClassifier.comp {α : Type u}
    {Generator1 Generator2 : α → α → Prop}
    {Classifier : α → Prop}
    (h1 : GeneratorClosureClassifier α Generator1 Classifier)
    (h2 : GeneratorClosureClassifier α Generator2 Classifier) :
    GeneratorClosureClassifier α
      (fun x y => ∃ z, Generator1 x z ∧ Generator2 z y)
      Classifier :=
  { closure := by
      intro x y hgen hclass
      obtain ⟨z, hg1, hg2⟩ := hgen
      exact h2.closure hg2 (h1.closure hg1 hclass) }

/-- Disjunctive union of two generators preserves any classifier that both preserve. -/
def GeneratorClosureClassifier.union {α : Type u}
    {Generator1 Generator2 : α → α → Prop}
    {Classifier : α → Prop}
    (h1 : GeneratorClosureClassifier α Generator1 Classifier)
    (h2 : GeneratorClosureClassifier α Generator2 Classifier) :
    GeneratorClosureClassifier α
      (fun x y => Generator1 x y ∨ Generator2 x y)
      Classifier :=
  { closure := by
      intro x y hgen hclass
      cases hgen with
      | inl hg => exact h1.closure hg hclass
      | inr hg => exact h2.closure hg hclass }

/-- Generator monotonicity: any sub-generator of a classifier-preserving generator
    is itself classifier-preserving. -/
def GeneratorClosureClassifier.weaken {α : Type u}
    {Generator1 Generator2 : α → α → Prop}
    {Classifier : α → Prop}
    (hsub : ∀ x y, Generator1 x y → Generator2 x y)
    (h2 : GeneratorClosureClassifier α Generator2 Classifier) :
    GeneratorClosureClassifier α Generator1 Classifier :=
  { closure := by
      intro x y hgen hclass
      exact h2.closure (hsub x y hgen) hclass }

end BEDC.MetaCIC
