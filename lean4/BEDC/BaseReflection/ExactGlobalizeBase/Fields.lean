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

end BEDC.BaseReflection
