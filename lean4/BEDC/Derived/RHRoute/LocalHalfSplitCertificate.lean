import BEDC.Derived.RHRoute.FunctionalEquationSymmetry

namespace BEDC.Derived.RHRoute.LocalHalfSplitCertificate

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.FunctionalEquationSymmetry

abbrev Rat : Type :=
  BEDC.Derived.RationalUp.RatNum

abbrev HalfSplitPoint : Type :=
  BEDC.Derived.RHRoute.FunctionalEquationSymmetry.RationalComplex

-- 作用域: 本文件只记录给定 `RationalComplex` 点的有理局部半分裂证书面。
-- 它不声称零点存在、解析延拓、精确零点判定或 RH 刚性命题。
structure LocalCriticalStrip (source : HalfSplitPoint) where
  above_lower : ratLe ratZero source.reAboveHalf
  above_upper : ratLe source.reAboveHalf ratOne
  below_lower : ratLe ratZero source.reBelowHalf
  below_upper : ratLe source.reBelowHalf ratOne

structure EndpointBisectionCertificate (source : HalfSplitPoint) where
  leftEndpoint : Rat
  rightEndpoint : Rat
  left_reads_source : RatEq leftEndpoint source.reAboveHalf
  right_reads_source : RatEq rightEndpoint source.reBelowHalf
  source_strip : LocalCriticalStrip source

namespace EndpointBisectionCertificate

def reassembled {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) : HalfSplitPoint where
  reAboveHalf := split.leftEndpoint
  reBelowHalf := split.rightEndpoint
  im := source.im

theorem reassembled_eq_source {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) :
    ComplexEq split.reassembled source := by
  exact And.intro split.left_reads_source
    (And.intro split.right_reads_source (SignedRatEq_refl source.im))

theorem endpoint_balance_iff_re_half {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) :
    RatEq split.leftEndpoint split.rightEndpoint ↔ ReEqHalf source := by
  constructor
  · intro balance
    have source_to_left : RatEq source.reAboveHalf split.leftEndpoint :=
      RatEq_symm split.left_reads_source
    have left_to_below : RatEq split.leftEndpoint source.reBelowHalf :=
      RatEq_trans split.leftEndpoint split.rightEndpoint source.reBelowHalf
        balance split.right_reads_source
    exact RatEq_trans source.reAboveHalf split.leftEndpoint
      source.reBelowHalf source_to_left left_to_below
  · intro half
    have left_to_below : RatEq split.leftEndpoint source.reBelowHalf :=
      RatEq_trans split.leftEndpoint source.reAboveHalf source.reBelowHalf
        split.left_reads_source half
    exact RatEq_trans split.leftEndpoint source.reBelowHalf
      split.rightEndpoint left_to_below (RatEq_symm split.right_reads_source)

theorem endpoint_balance_iff_JFixed {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) :
    RatEq split.leftEndpoint split.rightEndpoint ↔ JFixed source := by
  constructor
  · intro balance
    exact (J_fixed_iff_re_half source).mpr
      ((endpoint_balance_iff_re_half split).mp balance)
  · intro fixed
    exact (endpoint_balance_iff_re_half split).mpr
      ((J_fixed_iff_re_half source).mp fixed)

theorem endpoint_balance_iff_criticalLine {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) :
    RatEq split.leftEndpoint split.rightEndpoint ↔ CriticalLine source := by
  show RatEq split.leftEndpoint split.rightEndpoint ↔ ReEqHalf source
  exact endpoint_balance_iff_re_half split

structure EndpointLocalStrip {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) where
  left_lower : ratLe ratZero split.leftEndpoint
  left_upper : ratLe split.leftEndpoint ratOne
  right_lower : ratLe ratZero split.rightEndpoint
  right_upper : ratLe split.rightEndpoint ratOne

theorem endpoints_local_strip {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) :
    EndpointLocalStrip split := by
  exact
    { left_lower :=
        ratLe_respects (RatEq_refl ratZero)
          (RatEq_symm split.left_reads_source)
          split.source_strip.above_lower
      left_upper :=
        ratLe_respects (RatEq_symm split.left_reads_source) (RatEq_refl ratOne)
          split.source_strip.above_upper
      right_lower :=
        ratLe_respects (RatEq_refl ratZero)
          (RatEq_symm split.right_reads_source)
          split.source_strip.below_lower
      right_upper :=
        ratLe_respects (RatEq_symm split.right_reads_source) (RatEq_refl ratOne)
          split.source_strip.below_upper }

structure LocalSplitInvariant (source : HalfSplitPoint)
    (split : EndpointBisectionCertificate source) where
  reassembled_same_source : ComplexEq split.reassembled source
  source_local_strip : LocalCriticalStrip source
  endpoint_local_strip : EndpointLocalStrip split
  endpoint_balance_iff_fixed :
    RatEq split.leftEndpoint split.rightEndpoint ↔ JFixed source
  endpoint_balance_iff_criticalLine :
    RatEq split.leftEndpoint split.rightEndpoint ↔ CriticalLine source

theorem preserves_local_invariants {source : HalfSplitPoint}
    (split : EndpointBisectionCertificate source) :
    LocalSplitInvariant source split := by
  exact
    { reassembled_same_source := reassembled_eq_source split
      source_local_strip := split.source_strip
      endpoint_local_strip := endpoints_local_strip split
      endpoint_balance_iff_fixed := endpoint_balance_iff_JFixed split
      endpoint_balance_iff_criticalLine :=
        endpoint_balance_iff_criticalLine split }

end EndpointBisectionCertificate

structure LocalHalfSplitCertificate where
  source : HalfSplitPoint
  split : EndpointBisectionCertificate source
  fixed_half : JFixed source

namespace LocalHalfSplitCertificate

def reassembled (cert : LocalHalfSplitCertificate) : HalfSplitPoint :=
  cert.split.reassembled

theorem reassembled_eq_source (cert : LocalHalfSplitCertificate) :
    ComplexEq cert.reassembled cert.source :=
  EndpointBisectionCertificate.reassembled_eq_source cert.split

theorem endpoint_balance (cert : LocalHalfSplitCertificate) :
    RatEq cert.split.leftEndpoint cert.split.rightEndpoint := by
  exact (EndpointBisectionCertificate.endpoint_balance_iff_JFixed cert.split).mpr
    cert.fixed_half

theorem criticalLine (cert : LocalHalfSplitCertificate) :
    CriticalLine cert.source := by
  exact (criticalLine_J_fixed_iff cert.source).mp cert.fixed_half

end LocalHalfSplitCertificate

theorem localHalfSplitCertificate_preserves_invariants
    (cert : LocalHalfSplitCertificate) :
    EndpointBisectionCertificate.LocalSplitInvariant cert.source cert.split :=
  EndpointBisectionCertificate.preserves_local_invariants cert.split

theorem localHalfSplitCertificate_fixedHalf_to_bisection
    (cert : LocalHalfSplitCertificate) :
    RatEq cert.split.leftEndpoint cert.split.rightEndpoint :=
  cert.endpoint_balance

theorem localHalfSplitCertificate_fixedHalf_to_criticalLine
    (cert : LocalHalfSplitCertificate) :
    CriticalLine cert.source :=
  cert.criticalLine

end BEDC.Derived.RHRoute.LocalHalfSplitCertificate
