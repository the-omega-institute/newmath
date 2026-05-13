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

/-- The n-fold iteration of a generator as a binary relation.
    `IterRel G 0 x y` iff `x = y`;
    `IterRel G (n+1) x y` iff there exists `z` with `G x z` and
    `IterRel G n z y`. -/
def IterRel {α : Type u} (Generator : α → α → Prop) : Nat → α → α → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, Generator x z ∧ IterRel Generator n z y

/-- Finite iteration preserves classifier closure. -/
def GeneratorClosureClassifier.iterate {α : Type u}
    {Generator : α → α → Prop} {Classifier : α → Prop}
    (h : GeneratorClosureClassifier α Generator Classifier) :
    ∀ n, GeneratorClosureClassifier α (IterRel Generator n) Classifier
  | 0 =>
    { closure := by
        intro x y hgen hclass
        cases hgen
        exact hclass }
  | n + 1 =>
    { closure := by
        intro x y hgen hclass
        obtain ⟨z, hgz, hzy⟩ := hgen
        have hz : Classifier z := h.closure hgz hclass
        exact (iterate h n).closure hzy hz }

/-- Generator-closure classifier on a product carrier:
    closure under componentwise generator preserves the conjoined classifier. -/
def GeneratorClosureClassifier.product {α β : Type u}
    {Ga : α → α → Prop} {Gb : β → β → Prop}
    {Ca : α → Prop} {Cb : β → Prop}
    (ha : GeneratorClosureClassifier α Ga Ca)
    (hb : GeneratorClosureClassifier β Gb Cb) :
    GeneratorClosureClassifier (α × β)
      (fun p1 p2 => Ga p1.1 p2.1 ∧ Gb p1.2 p2.2)
      (fun p => Ca p.1 ∧ Cb p.2) :=
  { closure := by
      intro x y hgen hclass
      obtain ⟨hga, hgb⟩ := hgen
      obtain ⟨hca, hcb⟩ := hclass
      exact ⟨ha.closure hga hca, hb.closure hgb hcb⟩ }

/-- Generator-closure classifier on a disjoint sum carrier:
    case-split generator preserves case-split classifier. -/
def GeneratorClosureClassifier.sum {α β : Type u}
    {Ga : α → α → Prop} {Gb : β → β → Prop}
    {Ca : α → Prop} {Cb : β → Prop}
    (ha : GeneratorClosureClassifier α Ga Ca)
    (hb : GeneratorClosureClassifier β Gb Cb) :
    GeneratorClosureClassifier (α ⊕ β)
      (fun s1 s2 =>
        match s1, s2 with
        | Sum.inl a1, Sum.inl a2 => Ga a1 a2
        | Sum.inr b1, Sum.inr b2 => Gb b1 b2
        | _, _ => False)
      (fun s =>
        match s with
        | Sum.inl a => Ca a
        | Sum.inr b => Cb b) :=
  { closure := by
      intro x y hgen hclass
      cases x with
      | inl a =>
          cases y with
          | inl a' => exact ha.closure hgen hclass
          | inr b' => exact False.elim hgen
      | inr b =>
          cases y with
          | inl a' => exact False.elim hgen
          | inr b' => exact hb.closure hgen hclass }

end BEDC.MetaCIC
