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

theorem ExactGlobalizeBase_field_projection_pair
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ((forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q)) /\
      ((forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k)))) := by
  constructor
  · constructor
    · exact ex.coverage
    · exact ex.soundness
  · constructor
    · exact ex.completeness
    · intro h k p q hp hq
      exact ExactGlobalizeBase_classify_iff ex hp hq

theorem exact_globalize_base_target
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : forall h, s.InDom D h -> exists p, s.InGapSig P D p h)
    (soundness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      GeneratedSameSig s P h k -> PsameBase s P p q)
    (completeness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) :
    ExactGlobalizeBase s P D /\
      forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  · exact ExactGlobalizeBase_from_fields coverage soundness completeness
  · intro h k p q hp hq
    constructor
    · intro base
      exact completeness h k p q hp hq base
    · intro generated
      cases generated with
      | intro gen => exact soundness h k p q hp hq gen

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

theorem ExactGlobalizeBase_from_fields_admitted_pair_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h)
    (soundness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q)
    (completeness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k))
    {h k : s.Hist} (hdom : s.InDom D h) (kdom : s.InDom D k) :
    ExactGlobalizeBase s P D ∧ ∃ p : s.Pkg, ∃ q : s.Pkg,
      s.InGapSig P D p h ∧ s.InGapSig P D q k ∧
        (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  have ex : ExactGlobalizeBase s P D :=
    ExactGlobalizeBase_from_fields coverage soundness completeness
  cases coverage h hdom with
  | intro p hp =>
      cases coverage k kdom with
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

theorem NotExported_base_relation_pair {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D} (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) ∧
        (Nonempty (GeneratedSameSig s P h k) → PsameBase s P p q) := by
  intro hp hq
  have exactness : PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k) :=
    notExported hp hq
  constructor
  · intro base
    exact exactness.mp base
  · intro generated
    exact exactness.mpr generated

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

theorem ExactGlobalizeBase_notExported_public_shape
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    And (NotExported s P D ex)
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
          (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  · exact NotExported_from_exact ex
  · intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff ex hp hq

theorem not_exported {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) : NotExported s P D ex := by
  exact NotExported_from_exact ex

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

theorem ClosureReflect_preserves_base_sound_complete_pair
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) (_closure : ClosureReflect s P)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (Nonempty (GeneratedSameSig s P h k) → PsameBase s P p q) ∧
      (PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) := by
  have exactness : PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k) :=
    ExactGlobalizeBase_classify_iff ex hp hq
  constructor
  · intro generated
    exact exactness.mpr generated
  · intro base
    exact exactness.mp base

theorem ExactGlobalizeBase_no_closure_export_classification_iff
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  exact ExactGlobalizeBase_no_closure_export ex hp hq

theorem ExactGlobalizeBase_self_covered_classification
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h : s.Hist} :
    s.InDom D h → ∃ p : s.Pkg,
      s.InGapSig P D p h ∧
        (PsameBase s P p p ↔ Nonempty (GeneratedSameSig s P h h)) := by
  intro hdom
  cases ex.coverage h hdom with
  | intro p hp =>
      exact ⟨p, hp, ExactGlobalizeBase_classify_iff ex hp hp⟩

theorem ExactGlobalizeBase_local_sound_complete_classification
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (GeneratedSameSig s P h k → PsameBase s P p q) ∧
      (PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) ∧
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  · exact ex.soundness h k p q hp hq
  · constructor
    · exact ex.completeness h k p q hp hq
    · exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_from_fields_covered_classification
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h)
    (soundness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q)
    (completeness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k))
    {h k : s.Hist} (hdom : s.InDom D h) (kdom : s.InDom D k) :
    ∃ p : s.Pkg, ∃ q : s.Pkg,
      s.InGapSig P D p h ∧ s.InGapSig P D q k ∧
        (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  have ex : ExactGlobalizeBase s P D :=
    ExactGlobalizeBase_from_fields coverage soundness completeness
  cases coverage h hdom with
  | intro p hp =>
      cases coverage k kdom with
      | intro q hq =>
          exact Exists.intro p
            (Exists.intro q
              (And.intro hp
                (And.intro hq (ExactGlobalizeBase_classify_iff ex hp hq))))

end BEDC.BaseReflection
