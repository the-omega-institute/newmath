import BEDC.MetaCIC.Substitution.Core

namespace BEDC.MetaCIC

/-- 替换与提升交换的目标形状。 -/
def ShiftSubstituteStatement : Prop :=
  ∀ (n d : Idx) (v t : Term),
    n ≤ d →
    shift n 1 (substitute d v t) =
      substitute (d + 1) v (shift n 1 t)

/-- 替换复合的目标形状。 -/
def SubstituteSubstituteStatement : Prop :=
  ∀ (d : Idx) (s u t : Term),
    substitute d s (substitute (d + 1) u t) =
      substitute (d + 1) (shift d 1 s)
        (substitute d (substitute d s u) t)

end BEDC.MetaCIC
