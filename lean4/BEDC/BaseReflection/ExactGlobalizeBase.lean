import BEDC.BaseReflection.GeneratedSameSig

namespace BEDC.BaseReflection

structure ExactGlobalizeBase (s : BaseReflectionSetup) (P : s.Pi) (D : s.Domain) : Prop where
  coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h
  soundness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    GeneratedSameSig s P h k → PsameBase s P p q
  completeness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)

theorem ExactGlobalizeBase_soundness
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q := by
  exact ex.soundness

theorem ExactGlobalizeBase_soundness_exports_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    GeneratedSameSig s P h k → PsameBase s P p q := by
  intro hp hq gen
  exact ex.soundness h k p q hp hq gen

theorem ExactGlobalizeBase_soundness_nonempty
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    Nonempty (GeneratedSameSig s P h k) -> PsameBase s P p q := by
  intro hgen
  cases hgen with
  | intro gen =>
      exact ex.soundness h k p q hp hq gen

theorem ExactGlobalizeBase_export_soundness_direction
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    Nonempty (GeneratedSameSig s P h k) → PsameBase s P p q := by
  intro hgen
  cases hgen with
  | intro gen =>
      exact ex.soundness h k p q hp hq gen

theorem ExactGlobalizeBase_completeness
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k) := by
  intro hp hq base
  exact ex.completeness h k p q hp hq base

theorem ExactGlobalizeBase_sound_complete
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  case left =>
    intro gen
    exact ex.soundness h k p q hp hq gen
  case right =>
    intro base
    exact ex.completeness h k p q hp hq base

theorem ExactGlobalizeBase_from_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h)
    (soundness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q)
    (completeness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) :
    ExactGlobalizeBase s P D := by
  exact {
    coverage := coverage
    soundness := soundness
    completeness := completeness
  }

theorem ExactGlobalizeBase_constructor
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : forall h, s.InDom D h -> exists p, s.InGapSig P D p h)
    (soundness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      GeneratedSameSig s P h k -> PsameBase s P p q)
    (completeness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) :
    ExactGlobalizeBase s P D := by
  exact ExactGlobalizeBase_from_fields coverage soundness completeness

theorem ExactGlobalizeBase_coverage
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h := by
  exact ex.coverage

theorem ExactGlobalizeBase_coverage_projection
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D) :
    ∀ h : s.Hist, s.InDom D h → ∃ p : s.Pkg, s.InGapSig P D p h := by
  exact ex.coverage

theorem ExactGlobalizeBase_coverage_sound_complete
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (GeneratedSameSig s P h k -> PsameBase s P p q) /\
          (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    intro h k p q hp hq
    constructor
    case left =>
      intro gen
      exact ex.soundness h k p q hp hq gen
    case right =>
      intro base
      exact ex.completeness h k p q hp hq base

theorem ExactGlobalizeBase_coverage_sound_complete_classify
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D) :
    (∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h) ∧
      (∀ {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h → s.InGapSig P D q k →
          (GeneratedSameSig s P h k → PsameBase s P p q) ∧
          (PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) ∧
          (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  · exact ex.coverage
  · intro h k p q hp hq
    constructor
    · intro gen
      exact ex.soundness h k p q hp hq gen
    · constructor
      · intro base
        exact ex.completeness h k p q hp hq base
      · constructor
        · intro base
          exact ex.completeness h k p q hp hq base
        · intro generated
          cases generated with
          | intro gen =>
              exact ex.soundness h k p q hp hq gen

theorem no_scaffold_laundering_coverage_soundness
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q,
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) := by
  exact And.intro ex.coverage ex.soundness

theorem ExactGlobalizeBase_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    constructor
    case left =>
      exact ex.soundness
    case right =>
      exact ex.completeness

theorem ExactGlobalizeBase_iff_fields {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} :
    ExactGlobalizeBase s P D <->
      ((forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
        (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
          GeneratedSameSig s P h k -> PsameBase s P p q) /\
        (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
          PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case mp =>
    intro ex
    exact ExactGlobalizeBase_fields ex
  case mpr =>
    intro fields
    cases fields with
    | intro coverage rest =>
        cases rest with
        | intro soundness completeness =>
            exact ExactGlobalizeBase_from_fields coverage soundness completeness

theorem ExactGlobalizeBase_classify_iff
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k) := by
  constructor
  case mp =>
    intro hbase
    exact ex.completeness h k p q hp hq hbase
  case mpr =>
    intro hgen
    cases hgen with
    | intro hsig =>
        exact ex.soundness h k p q hp hq hsig

theorem ExactGlobalizeBase_symmetric_classify_iff
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (eqv : HSameEquiv s)
    (ex : ExactGlobalizeBase s P D) {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    PsameBase s P q p ↔ Nonempty (GeneratedSameSig s P k h) := by
  constructor
  case mp =>
    intro base
    have forwardBase : PsameBase s P p q := PsameBase_symm_under_equiv eqv base
    have forwardGen : Nonempty (GeneratedSameSig s P h k) :=
      ex.completeness h k p q hp hq forwardBase
    exact GeneratedSameSig_symm_nonempty eqv forwardGen
  case mpr =>
    intro generated
    have forwardGen : Nonempty (GeneratedSameSig s P h k) :=
      GeneratedSameSig_symm_nonempty eqv generated
    have forwardBase : PsameBase s P p q := by
      cases forwardGen with
      | intro gen =>
          exact ex.soundness h k p q hp hq gen
    exact PsameBase_symm_under_equiv eqv forwardBase

theorem ExactGlobalizeBase_coverage_and_classification
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D) :
    (∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h) ∧
      (∀ {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h → s.InGapSig P D q k →
          (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_classification_four_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D) :
    (∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h) ∧
      (∀ h k p q, s.InGapSig P D p h → s.InGapSig P D q k →
        GeneratedSameSig s P h k → PsameBase s P p q) ∧
      (∀ h k p q, s.InGapSig P D p h → s.InGapSig P D q k →
        PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) ∧
      (∀ {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h → s.InGapSig P D q k →
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

theorem ExactGlobalizeBase_classify_directions
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) /\
      (Nonempty (GeneratedSameSig s P h k) -> PsameBase s P p q) := by
  constructor
  case left =>
    exact (ExactGlobalizeBase_classify_iff ex hp hq).mp
  case right =>
    exact (ExactGlobalizeBase_classify_iff ex hp hq).mpr

theorem no_scaffold_laundering_fields_and_classifier
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ((forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  exact And.intro
    (ExactGlobalizeBase_fields ex)
    (fun {h k : s.Hist} {p q : s.Pkg}
      (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) =>
        ExactGlobalizeBase_classify_iff ex hp hq)

theorem ExactGlobalizeBase_from_fields_classify_iff
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : forall h, s.InDom D h -> exists p, s.InGapSig P D p h)
    (soundness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      GeneratedSameSig s P h k -> PsameBase s P p q)
    (completeness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k) := by
  exact ExactGlobalizeBase_classify_iff
    (ExactGlobalizeBase_from_fields coverage soundness completeness) hp hq

theorem globalize_exact_base
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
  case left =>
    exact ExactGlobalizeBase_from_fields coverage soundness completeness
  case right =>
    intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff
      (ExactGlobalizeBase_from_fields coverage soundness completeness) hp hq

theorem ExactGlobalizeBase_target
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h)
    (soundness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q)
    (completeness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) :
    ExactGlobalizeBase s P D ∧
      ∀ {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h → s.InGapSig P D q k →
        (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  exact globalize_exact_base coverage soundness completeness

theorem Globalize.exactBase
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
  exact globalize_exact_base coverage soundness completeness

theorem ExactGlobalizeBase_classify_iff_from_directions
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (soundness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q)
    (completeness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k))
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k) := by
  constructor
  case mp =>
    intro hbase
    exact completeness h k p q hp hq hbase
  case mpr =>
    intro hgen
    cases hgen with
    | intro hsig =>
        exact soundness h k p q hp hq hsig

theorem ExactGlobalizeBase_exports_base_relation
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_no_closure_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_no_closure_export_directions
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
          PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
          Nonempty (GeneratedSameSig s P h k) -> PsameBase s P p q) := by
  constructor
  case left =>
    intro h k p q hp hq base
    have exactness :
        PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k) :=
      ExactGlobalizeBase_no_closure_export ex hp hq
    exact exactness.mp base
  case right =>
    intro h k p q hp hq generated
    have exactness :
        PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k) :=
      ExactGlobalizeBase_no_closure_export ex hp hq
    exact exactness.mpr generated

theorem ExactGlobalizeBase_no_eqClosure_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem no_implicit_closure_exports_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_relation_is_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

def NotExported (s : BaseReflectionSetup) (P : s.Pi) (D : s.Domain)
    (_ex : ExactGlobalizeBase s P D) : Prop :=
  forall {h k : s.Hist} {p q : s.Pkg},
    s.InGapSig P D p h -> s.InGapSig P D q k ->
      (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))

theorem NotExported_from_exact
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) : NotExported s P D ex := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem NotExported_from_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : forall h, s.InDom D h -> exists p, s.InGapSig P D p h)
    (soundness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      GeneratedSameSig s P h k -> PsameBase s P p q)
    (completeness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) :
    NotExported s P D (ExactGlobalizeBase_from_fields coverage soundness completeness) := by
  exact NotExported_from_exact (ExactGlobalizeBase_from_fields coverage soundness completeness)

theorem NotExported_classify_iff {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D} (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro hp hq
  exact notExported hp hq

theorem NotExported_relation_is_base {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D} (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h -> s.InGapSig P D q k ->
    (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k)) := by
  intro hp hq
  exact notExported hp hq

theorem NotExported_base_to_GeneratedSameSig {s : BaseReflectionSetup} {P : s.Pi}
    {D : s.Domain} {ex : ExactGlobalizeBase s P D} (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k) := by
  exact fun hp hq base => (notExported hp hq).mp base

theorem NotExported_GeneratedSameSig_to_base {s : BaseReflectionSetup} {P : s.Pi}
    {D : s.Domain} {ex : ExactGlobalizeBase s P D} (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    Nonempty (GeneratedSameSig s P h k) → PsameBase s P p q := by
  exact fun hp hq gen => (notExported hp hq).mpr gen
theorem NotExported_classify_directions {s : BaseReflectionSetup} {P : s.Pi}
    {D : s.Domain} {ex : ExactGlobalizeBase s P D} (notExported : NotExported s P D ex) :
    (forall {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) /\
    (forall {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      Nonempty (GeneratedSameSig s P h k) -> PsameBase s P p q) := by
  exact And.intro
    (fun hp hq base => (notExported hp hq).mp base)
    (fun hp hq generated => (notExported hp hq).mpr generated)


theorem NotExported_no_eqClosure_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D}
    (notExported : NotExported s P D ex) :
    forall {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact notExported hp hq

theorem ClosureReflect_preserves_base_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) (_closure : ClosureReflect s P) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_exact
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  exact And.intro ex.coverage (by
    intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff ex hp hq)

theorem ExactGlobalizeBase_public_export_shape
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_export_from_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} :
    ((forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) ->
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  intro fields
  cases fields with
  | intro coverage rest =>
      cases rest with
      | intro soundness completeness =>
          exact And.intro coverage (by
            intro h k p q hp hq
            constructor
            case mp =>
              intro base
              exact completeness h k p q hp hq base
            case mpr =>
              intro generated
              cases generated with
              | intro gen =>
                  exact soundness h k p q hp hq gen)

end BEDC.BaseReflection
