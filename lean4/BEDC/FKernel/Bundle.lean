/-! Probe bundles are internally generated records, not exposed host lists. -/
namespace BEDC.FKernel.Bundle

inductive ProbeBundle (PName : Type) where
  | Bnil
  | Bcons (p : PName) (b : ProbeBundle PName)

def InBundle {PName : Type} (p : PName) : ProbeBundle PName → Prop
  | .Bnil => False
  | .Bcons q b => p = q ∨ InBundle p b

def bundleAppend {PName : Type} : ProbeBundle PName → ProbeBundle PName → ProbeBundle PName
  | .Bnil, right => right
  | .Bcons p tail, right => .Bcons p (bundleAppend tail right)

def bundleLength {PName : Type} : ProbeBundle PName → Nat
  | .Bnil => 0
  | .Bcons _ tail => Nat.succ (bundleLength tail)

theorem bundleLength_append {PName : Type} :
    ∀ left right : ProbeBundle PName,
      bundleLength (bundleAppend left right) = bundleLength left + bundleLength right := by
  intro left
  induction left with
  | Bnil =>
      intro right
      exact (Nat.zero_add (bundleLength right)).symm
  | Bcons p tail ih =>
      intro right
      exact Eq.trans (congrArg Nat.succ (ih right))
        (Eq.symm (Nat.succ_add (bundleLength tail) (bundleLength right)))

theorem bundleLength_bundleAppend {PName : Type} :
    ∀ left right : ProbeBundle PName,
      bundleLength (bundleAppend left right) = bundleLength left + bundleLength right := by
  exact bundleLength_append

theorem bundleAppend_length {PName : Type} :
    ∀ left right : ProbeBundle PName,
      bundleLength (bundleAppend left right) = bundleLength left + bundleLength right := by
  exact bundleLength_append

theorem bundleAppend_nil_right {PName : Type} :
    ∀ bundle : ProbeBundle PName, bundleAppend bundle ProbeBundle.Bnil = bundle := by
  intro bundle
  induction bundle with
  | Bnil =>
      rfl
  | Bcons p tail ih =>
      exact congrArg (ProbeBundle.Bcons p) ih

theorem bundleAppend_assoc {PName : Type} :
    ∀ left middle right : ProbeBundle PName,
      bundleAppend (bundleAppend left middle) right =
        bundleAppend left (bundleAppend middle right) := by
  intro left
  induction left with
  | Bnil =>
      intro middle right
      rfl
  | Bcons p tail ih =>
      intro middle right
      exact congrArg (ProbeBundle.Bcons p) (ih middle right)

theorem bundleAppend_right_nil {PName : Type} :
    forall bundle : ProbeBundle PName,
      bundleAppend bundle (ProbeBundle.Bnil : ProbeBundle PName) = bundle := by
  intro bundle
  induction bundle with
  | Bnil =>
      rfl
  | Bcons p tail ih =>
      exact congrArg (ProbeBundle.Bcons p) ih

theorem bundleAppend_prefix_cancel {PName : Type} :
    ∀ pref left right : ProbeBundle PName,
      bundleAppend pref left = bundleAppend pref right → left = right := by
  intro pref
  induction pref with
  | Bnil =>
      intro left right same
      exact same
  | Bcons p tail ih =>
      intro left right same
      exact ih left right (ProbeBundle.Bcons.inj same).right

theorem bundleAppend_cons_result_inversion {PName : Type}
    {pref suff out : ProbeBundle PName} {p : PName} :
    bundleAppend pref suff = ProbeBundle.Bcons p out ->
      (pref = ProbeBundle.Bnil ∧ suff = ProbeBundle.Bcons p out) ∨
        ∃ pref0 : ProbeBundle PName,
          pref = ProbeBundle.Bcons p pref0 ∧ bundleAppend pref0 suff = out := by
  intro same
  cases pref with
  | Bnil =>
      exact Or.inl (And.intro rfl same)
  | Bcons q pref0 =>
      cases same
      exact Or.inr (Exists.intro pref0 (And.intro rfl rfl))

theorem bundleAppend_empty_result_inversion {PName : Type}
    {left right : ProbeBundle PName} :
    bundleAppend left right = ProbeBundle.Bnil →
      left = ProbeBundle.Bnil ∧ right = ProbeBundle.Bnil := by
  intro same
  cases left with
  | Bnil =>
      exact And.intro rfl same
  | Bcons p tail =>
      cases same

theorem inBundle_bundleAppend_iff {PName : Type} {p : PName}
    {left right : ProbeBundle PName} :
    InBundle p (bundleAppend left right) ↔ InBundle p left ∨ InBundle p right := by
  induction left with
  | Bnil =>
      constructor
      · intro h
        exact Or.inr h
      · intro h
        cases h with
        | inl hleft =>
            exact False.elim hleft
        | inr hright =>
            exact hright
  | Bcons q tail ih =>
      constructor
      · intro h
        cases h with
        | inl hpq =>
            exact Or.inl (Or.inl hpq)
        | inr htail =>
            cases ih.mp htail with
            | inl hleft =>
                exact Or.inl (Or.inr hleft)
            | inr hright =>
                exact Or.inr hright
      · intro h
        cases h with
        | inl hleft =>
            cases hleft with
            | inl hpq =>
                exact Or.inl hpq
            | inr htail =>
                exact Or.inr (ih.mpr (Or.inl htail))
        | inr hright =>
            exact Or.inr (ih.mpr (Or.inr hright))

theorem inBundle_nil_elim {PName : Type} {p : PName} :
    InBundle p (ProbeBundle.Bnil : ProbeBundle PName) → False := by
  intro h
  exact h

theorem inBundle_nil_false {PName : Type} {p : PName} :
    InBundle p (ProbeBundle.Bnil : ProbeBundle PName) → False := by
  intro h
  exact h

theorem inBundle_cons_self {PName : Type} (p : PName) (tail : ProbeBundle PName) :
    InBundle p (ProbeBundle.Bcons p tail) := by
  exact Or.inl rfl

theorem inBundle_cons_of_eq {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    p = q -> InBundle p (ProbeBundle.Bcons q tail) := by
  intro hp
  exact Or.inl hp

theorem inBundle_singleton_iff {PName : Type} {p q : PName} :
    InBundle p (ProbeBundle.Bcons q (ProbeBundle.Bnil : ProbeBundle PName)) ↔ p = q := by
  constructor
  · intro h
    cases h with
    | inl hp =>
        exact hp
    | inr hnil =>
        exact False.elim hnil
  · intro hp
    exact inBundle_cons_of_eq hp

theorem inBundle_cons_tail {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p tail -> InBundle p (ProbeBundle.Bcons q tail) := by
  intro h
  exact Or.inr h

theorem inBundle_cons_cons_tail {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x tail → InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) := by
  intro h
  exact Or.inr (Or.inr h)

theorem inBundle_cons_cons_tail_iff_of_head_ne {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    x ≠ p →
      (InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) ↔
        x = q ∨ InBundle x tail) := by
  intro hne
  constructor
  · intro h
    cases h with
    | inl hp =>
        exact False.elim (hne hp)
    | inr htail =>
        exact htail
  · intro h
    exact Or.inr h

theorem inBundle_cons_inversion {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p (ProbeBundle.Bcons q tail) -> p = q \/ InBundle p tail := by
  intro h
  exact h

theorem inBundle_tail_of_cons_ne {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p (ProbeBundle.Bcons q tail) -> p ≠ q -> InBundle p tail := by
  intro h hne
  cases h with
  | inl hp =>
      exact False.elim (hne hp)
  | inr htail =>
      exact htail

theorem inBundle_cons_tail_iff_of_ne {PName : Type} {p q : PName}
    {tail : ProbeBundle PName} :
    p ≠ q → (InBundle p (ProbeBundle.Bcons q tail) ↔ InBundle p tail) := by
  intro hne
  constructor
  · intro h
    exact inBundle_tail_of_cons_ne h hne
  · intro h
    exact inBundle_cons_tail h

theorem inBundle_cons_iff {PName : Type} {p q : PName} {tail : ProbeBundle PName} :
    InBundle p (ProbeBundle.Bcons q tail) ↔ p = q ∨ InBundle p tail := by
  rfl

theorem inBundle_cons_cons_iff {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) ↔
      x = p ∨ x = q ∨ InBundle x tail := by
  rfl

theorem inBundle_cons_cons_inversion {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) →
      x = p ∨ x = q ∨ InBundle x tail := by
  intro h
  exact h

theorem inBundle_cons_cons_swap {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) →
      x = q ∨ x = p ∨ InBundle x tail := by
  intro h
  cases h with
  | inl hp =>
      exact Or.inr (Or.inl hp)
  | inr htail =>
      cases htail with
      | inl hq =>
          exact Or.inl hq
      | inr hrest =>
          exact Or.inr (Or.inr hrest)

theorem inBundle_cons_cons_comm {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) ↔
      InBundle x (ProbeBundle.Bcons q (ProbeBundle.Bcons p tail)) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
        exact Or.inr (Or.inl hp)
    | inr htail =>
        cases htail with
        | inl hq =>
            exact Or.inl hq
        | inr hrest =>
            exact Or.inr (Or.inr hrest)
  · intro h
    cases h with
    | inl hq =>
        exact Or.inr (Or.inl hq)
    | inr htail =>
        cases htail with
        | inl hp =>
            exact Or.inl hp
        | inr hrest =>
            exact Or.inr (Or.inr hrest)

theorem inBundle_cons_cons_swap_iff {PName : Type} {x p q : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons p (ProbeBundle.Bcons q tail)) ↔
      InBundle x (ProbeBundle.Bcons q (ProbeBundle.Bcons p tail)) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
        exact Or.inr (Or.inl hp)
    | inr htail =>
        cases htail with
        | inl hq =>
            exact Or.inl hq
        | inr hrest =>
            exact Or.inr (Or.inr hrest)
  · intro h
    cases h with
    | inl hq =>
        exact Or.inr (Or.inl hq)
    | inr htail =>
        cases htail with
        | inl hp =>
            exact Or.inl hp
        | inr hrest =>
            exact Or.inr (Or.inr hrest)

theorem inBundle_cons_three_rotate {PName : Type} {x a b c : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons a (ProbeBundle.Bcons b (ProbeBundle.Bcons c tail))) →
      InBundle x (ProbeBundle.Bcons c (ProbeBundle.Bcons a (ProbeBundle.Bcons b tail))) := by
  intro h
  cases h with
  | inl ha =>
      exact Or.inr (Or.inl ha)
  | inr htail =>
      cases htail with
      | inl hb =>
          exact Or.inr (Or.inr (Or.inl hb))
      | inr hrest =>
          cases hrest with
          | inl hc =>
              exact Or.inl hc
          | inr htail =>
              exact Or.inr (Or.inr (Or.inr htail))

theorem inBundle_cons_three_rotate_iff {PName : Type} {x a b c : PName}
    {tail : ProbeBundle PName} :
    InBundle x (ProbeBundle.Bcons a (ProbeBundle.Bcons b (ProbeBundle.Bcons c tail))) ↔
      InBundle x (ProbeBundle.Bcons c (ProbeBundle.Bcons a (ProbeBundle.Bcons b tail))) := by
  constructor
  · intro h
    exact inBundle_cons_three_rotate h
  · intro h
    cases h with
    | inl hc =>
        exact Or.inr (Or.inr (Or.inl hc))
    | inr htail =>
        cases htail with
        | inl ha =>
            exact Or.inl ha
        | inr hrest =>
            cases hrest with
            | inl hb =>
                exact Or.inr (Or.inl hb)
            | inr htail =>
                exact Or.inr (Or.inr (Or.inr htail))

theorem inBundle_cons_three_head_or_tail {PName : Type} {x a b c : PName} :
    InBundle x
        (ProbeBundle.Bcons a (ProbeBundle.Bcons b (ProbeBundle.Bcons c ProbeBundle.Bnil))) →
      x = a ∨ x = b ∨ x = c := by
  intro h
  cases h with
  | inl ha =>
      exact Or.inl ha
  | inr htail =>
      cases htail with
      | inl hb =>
          exact Or.inr (Or.inl hb)
      | inr hrest =>
          cases hrest with
          | inl hc =>
              exact Or.inr (Or.inr hc)
          | inr hnil =>
              exact False.elim hnil

theorem inBundle_cons_four_head_or_tail {PName : Type} {x a b c d : PName} :
    InBundle x
        (ProbeBundle.Bcons a
          (ProbeBundle.Bcons b (ProbeBundle.Bcons c (ProbeBundle.Bcons d ProbeBundle.Bnil)))) →
      x = a ∨ x = b ∨ x = c ∨ x = d := by
  intro h
  cases h with
  | inl ha =>
      exact Or.inl ha
  | inr htail =>
      cases htail with
      | inl hb =>
          exact Or.inr (Or.inl hb)
      | inr hrest =>
          cases hrest with
          | inl hc =>
              exact Or.inr (Or.inr (Or.inl hc))
          | inr hmore =>
              cases hmore with
              | inl hd =>
                  exact Or.inr (Or.inr (Or.inr hd))
              | inr hnil =>
                  exact False.elim hnil

theorem inBundle_cons_four_rotate_iff {PName : Type} {x a b c d : PName}
    {tail : ProbeBundle PName} :
    InBundle x
        (ProbeBundle.Bcons a
          (ProbeBundle.Bcons b (ProbeBundle.Bcons c (ProbeBundle.Bcons d tail)))) ↔
      InBundle x
        (ProbeBundle.Bcons b
          (ProbeBundle.Bcons c (ProbeBundle.Bcons d (ProbeBundle.Bcons a tail)))) := by
  constructor
  · intro h
    cases h with
    | inl ha =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    | inr htail =>
        cases htail with
        | inl hb =>
            exact Or.inl hb
        | inr hrest =>
            cases hrest with
            | inl hc =>
                exact Or.inr (Or.inl hc)
            | inr hmore =>
                cases hmore with
                | inl hd =>
                    exact Or.inr (Or.inr (Or.inl hd))
                | inr htail =>
                    exact Or.inr (Or.inr (Or.inr (Or.inr htail)))
  · intro h
    cases h with
    | inl hb =>
        exact Or.inr (Or.inl hb)
    | inr htail =>
        cases htail with
        | inl hc =>
            exact Or.inr (Or.inr (Or.inl hc))
        | inr hrest =>
            cases hrest with
            | inl hd =>
                exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
            | inr hmore =>
                cases hmore with
                | inl ha =>
                    exact Or.inl ha
                | inr htail =>
                    exact Or.inr (Or.inr (Or.inr (Or.inr htail)))

theorem inBundle_nonempty_from_membership {PName : Type} {p : PName} :
    ∀ {bundle : ProbeBundle PName}, InBundle p bundle →
      ∃ q : PName, ∃ tail : ProbeBundle PName, bundle = ProbeBundle.Bcons q tail := by
  intro bundle h
  cases bundle with
  | Bnil =>
      exact False.elim h
  | Bcons q tail =>
      exact ⟨q, tail, rfl⟩

theorem bundle_generation_cases {PName : Type} (bundle : ProbeBundle PName) :
    bundle = ProbeBundle.Bnil ∨
      ∃ p : PName, ∃ tail : ProbeBundle PName, bundle = ProbeBundle.Bcons p tail := by
  cases bundle with
  | Bnil =>
      exact Or.inl rfl
  | Bcons p tail =>
      exact Or.inr ⟨p, tail, rfl⟩

theorem bundle_generation_head_tail_pair {PName : Type} :
    (∀ (p : PName) (tail : ProbeBundle PName), InBundle p (ProbeBundle.Bcons p tail)) ∧
      (∀ {p q : PName} {tail : ProbeBundle PName}, InBundle p tail →
        InBundle p (ProbeBundle.Bcons q tail)) := by
  constructor
  · intro p tail
    exact Or.inl rfl
  · intro p q tail h
    exact Or.inr h

theorem probeBundle_nil_ne_cons {PName : Type} {p : PName} {tail : ProbeBundle PName} :
    ProbeBundle.Bnil ≠ ProbeBundle.Bcons p tail := by
  intro h
  cases h

theorem probeBundle_no_confusion_all {PName : Type} :
    (∀ {p : PName} {tail : ProbeBundle PName},
      ProbeBundle.Bnil ≠ ProbeBundle.Bcons p tail) ∧
      (∀ {p : PName} {tail : ProbeBundle PName},
        ProbeBundle.Bcons p tail ≠ ProbeBundle.Bnil) ∧
        (∀ {p q : PName} {tail tail' : ProbeBundle PName},
          ProbeBundle.Bcons p tail = ProbeBundle.Bcons q tail' → p = q ∧ tail = tail') := by
  constructor
  · intro p tail h
    cases h
  · constructor
    · intro p tail h
      cases h
    · intro p q tail tail' h
      cases h
      exact ⟨rfl, rfl⟩

theorem probeBundle_cons_injective_pair {PName : Type} {p q : PName}
    {tail tail' : ProbeBundle PName} :
    ProbeBundle.Bcons p tail = ProbeBundle.Bcons q tail' → p = q ∧ tail = tail' := by
  intro h
  cases h
  exact ⟨rfl, rfl⟩

theorem probeBundle_cons_injective {PName : Type} {p q : PName}
    {tail tail' : ProbeBundle PName} :
    ProbeBundle.Bcons p tail = ProbeBundle.Bcons q tail' → p = q /\ tail = tail' := by
  intro h
  cases h
  exact ⟨rfl, rfl⟩

theorem probeBundle_cons_ne_self {PName : Type} :
    ∀ (p : PName) (tail : ProbeBundle PName), ProbeBundle.Bcons p tail ≠ tail := by
  intro p tail
  induction tail generalizing p with
  | Bnil =>
      intro h
      cases h
  | Bcons q tail ih =>
      intro h
      exact ih q (ProbeBundle.Bcons.inj h).right

theorem probeBundle_two_cons_ne_tail {PName : Type} :
    ∀ (p q : PName) (tail : ProbeBundle PName),
      ProbeBundle.Bcons p (ProbeBundle.Bcons q tail) ≠ tail := by
  intro p q tail
  induction tail generalizing p q with
  | Bnil =>
      intro h
      cases h
  | Bcons r tail ih =>
      intro h
      exact ih q r (ProbeBundle.Bcons.inj h).right

theorem probeBundle_three_cons_ne_tail {PName : Type} :
    ∀ (p q r : PName) (tail : ProbeBundle PName),
      ProbeBundle.Bcons p (ProbeBundle.Bcons q (ProbeBundle.Bcons r tail)) ≠ tail := by
  intro p q r tail
  induction tail generalizing p q r with
  | Bnil =>
      intro h
      cases h
  | Bcons s tail ih =>
      intro h
      exact ih q r s (ProbeBundle.Bcons.inj h).right

theorem probeBundle_generated_induction {PName : Type} {M : ProbeBundle PName → Prop} :
    M ProbeBundle.Bnil →
      (∀ p tail, M tail → M (ProbeBundle.Bcons p tail)) →
        ∀ bundle, M bundle := by
  intro hnil hcons bundle
  induction bundle with
  | Bnil =>
      exact hnil
  | Bcons p tail ih =>
      exact hcons p tail ih

theorem bundle_generation_cases_and_induction {PName : Type} {M : ProbeBundle PName → Prop} :
    (∀ bundle : ProbeBundle PName, bundle = ProbeBundle.Bnil ∨
      ∃ p : PName, ∃ tail : ProbeBundle PName, bundle = ProbeBundle.Bcons p tail) ∧
      (M ProbeBundle.Bnil →
        (∀ p tail, M tail → M (ProbeBundle.Bcons p tail)) → ∀ bundle, M bundle) := by
  constructor
  · exact bundle_generation_cases
  · exact probeBundle_generated_induction

theorem bundle_generation_tail_induction_pair {PName : Type} {M : ProbeBundle PName → Prop}
    (nil : M ProbeBundle.Bnil)
    (cons : ∀ (p : PName) (tail : ProbeBundle PName), M tail → M (ProbeBundle.Bcons p tail)) :
    (∀ bundle : ProbeBundle PName, M bundle) ∧
      (∀ (p : PName) (tail : ProbeBundle PName), M tail → M (ProbeBundle.Bcons p tail)) := by
  constructor
  · intro bundle
    induction bundle with
    | Bnil =>
        exact nil
    | Bcons p tail ih =>
        exact cons p tail ih
  · intro p tail htail
    exact cons p tail htail

end BEDC.FKernel.Bundle
