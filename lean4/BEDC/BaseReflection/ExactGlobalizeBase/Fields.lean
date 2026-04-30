import BEDC.BaseReflection.ExactGlobalizeBase

namespace BEDC.BaseReflection

theorem ExactGlobalizeBase_four_field_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h) ∧
      (∀ h k p q, s.InGapSig P D p h → s.InGapSig P D q k →
        GeneratedSameSig s P h k → PsameBase s P p q) ∧
      (∀ h k p q, s.InGapSig P D p h → s.InGapSig P D q k →
        PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) ∧
      (∀ h k p q, s.InGapSig P D p h → s.InGapSig P D q k →
        (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    constructor
    case left =>
      exact ex.soundness
    case right =>
      constructor
      case left =>
        exact ex.completeness
      case right =>
        intro h k p q hp hq
        exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_covered_classification
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist}
    (hdom : s.InDom D h) (kdom : s.InDom D k) :
    ∃ p : s.Pkg, ∃ q : s.Pkg,
      s.InGapSig P D p h ∧ s.InGapSig P D q k ∧
        (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  cases ex.coverage h hdom with
  | intro p hp =>
      cases ex.coverage k kdom with
      | intro q hq =>
          exact ⟨p, q, hp, hq, ExactGlobalizeBase_classify_iff ex hp hq⟩

theorem ExactGlobalizeBase_admitted_pair_export_shape
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist}
    (hdom : s.InDom D h) (kdom : s.InDom D k) :
    ExactGlobalizeBase s P D /\ ∃ p : s.Pkg, ∃ q : s.Pkg,
      s.InGapSig P D p h ∧ s.InGapSig P D q k ∧
        (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  cases ex.coverage h hdom with
  | intro p hp =>
      cases ex.coverage k kdom with
      | intro q hq =>
          exact ⟨ex, p, q, hp, hq, ExactGlobalizeBase_classify_iff ex hp hq⟩

theorem ExactGlobalizeBase_covered_sound_complete
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist}
    (hdom : s.InDom D h) (kdom : s.InDom D k) :
    ∃ p : s.Pkg, ∃ q : s.Pkg,
      s.InGapSig P D p h ∧ s.InGapSig P D q k ∧
        ((GeneratedSameSig s P h k → PsameBase s P p q) ∧
          (PsameBase s P p q → Nonempty (GeneratedSameSig s P h k))) := by
  cases ex.coverage h hdom with
  | intro p hp =>
      cases ex.coverage k kdom with
      | intro q hq =>
          exact ⟨p, q, hp, hq, ExactGlobalizeBase_sound_complete ex hp hq⟩

theorem ExactGlobalizeBase_covered_soundness_direction
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist}
    (hdom : s.InDom D h) (kdom : s.InDom D k) :
    ∃ p : s.Pkg, ∃ q : s.Pkg,
      s.InGapSig P D p h ∧ s.InGapSig P D q k ∧
        (GeneratedSameSig s P h k → PsameBase s P p q) := by
  cases ex.coverage h hdom with
  | intro p hp =>
      cases ex.coverage k kdom with
      | intro q hq =>
          exact ⟨p, q, hp, hq, ex.soundness h k p q hp hq⟩

theorem ExactGlobalizeBase_covered_completeness_direction
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist}
    (hdom : s.InDom D h) (kdom : s.InDom D k) :
    exists p : s.Pkg, exists q : s.Pkg,
      s.InGapSig P D p h /\ s.InGapSig P D q k /\
        (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) := by
  cases ex.coverage h hdom with
  | intro p hp =>
      cases ex.coverage k kdom with
      | intro q hq =>
          exact ⟨p, q, hp, hq, ex.completeness h k p q hp hq⟩

theorem ExactGlobalizeBase_covered_classification_directions
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist}
    (hdom : s.InDom D h) (kdom : s.InDom D k) :
    ∃ p : s.Pkg, ∃ q : s.Pkg,
      s.InGapSig P D p h ∧ s.InGapSig P D q k ∧
        (GeneratedSameSig s P h k → PsameBase s P p q) ∧
        (PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) ∧
        (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  cases ex.coverage h hdom with
  | intro p hp =>
      cases ex.coverage k kdom with
      | intro q hq =>
          exact ⟨p, q, hp, hq, ex.soundness h k p q hp hq,
            ex.completeness h k p q hp hq, ExactGlobalizeBase_classify_iff ex hp hq⟩

theorem NotExported_sound_complete_pair
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D}
    (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  · intro generated
    exact (notExported hp hq).mpr (Nonempty.intro generated)
  · intro base
    exact (notExported hp hq).mp base

theorem ExactGlobalizeBase_sound_complete_and_classify
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    And (And (GeneratedSameSig s P h k -> PsameBase s P p q)
      (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)))
      (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k)) := by
  exact And.intro
    (ExactGlobalizeBase_sound_complete ex hp hq)
    (ExactGlobalizeBase_classify_iff ex hp hq)

theorem checked_acceptance_gate_exactBase_exports_public_shape
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ExactGlobalizeBase s P D ∧
    (forall {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  · exact ex
  · intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_no_closure_export_sound_complete_pair
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (Nonempty (GeneratedSameSig s P h k) -> PsameBase s P p q) ∧
      (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) := by
  have exactness :
      PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k) :=
    ExactGlobalizeBase_no_closure_export ex hp hq
  constructor
  · intro generated
    exact exactness.mpr generated
  · intro base
    exact exactness.mp base

end BEDC.BaseReflection
