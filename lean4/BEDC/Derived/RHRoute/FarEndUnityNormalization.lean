import BEDC.Derived.RHRoute.UnitaryBalance
import BEDC.Derived.TranscendentalFarEndUp

namespace BEDC.Derived.RHRoute.FarEndUnityNormalization

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev PrimeLocalChannel :=
  BEDC.Derived.RHRoute.UnitaryBalance.PrimeLocalChannel

abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.UnitaryBalance.UnitaryBalanceSurface

abbrev TranscendentalFarEndSocket :=
  BEDC.Derived.TranscendentalFarEndUp.TranscendentalFarEndSocket

def PrimeWindowUnitNorm (channel : PrimeLocalChannel) : Prop :=
  BEDC.Derived.RationalUp.RatEq
    (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow channel)
    BEDC.Derived.RationalUp.ratOne

/--
素窗口归一化只记录已经给出的单位范数见证。这里不从任意通道制造单位范数,
也不把远端边界读成内部元素。
-/
structure PrimeWindowNormalization where
  sourceWindow : PrimeWindow
  normalizedChannel : PrimeLocalChannel
  window_preserved : normalizedChannel.window = sourceWindow
  unit_norm : PrimeWindowUnitNorm normalizedChannel

def PrimeWindowNormalization.toUnitaryBalanceSurface
    (normalization : PrimeWindowNormalization) : UnitaryBalanceSurface where
  channel := normalization.normalizedChannel
  norm_one := normalization.unit_norm

theorem PrimeWindowNormalization.normalized_window
    (normalization : PrimeWindowNormalization) :
    normalization.normalizedChannel.window = normalization.sourceWindow :=
  normalization.window_preserved

theorem PrimeWindowNormalization.unit_norm_transfers
    (normalization : PrimeWindowNormalization) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        normalization.normalizedChannel)
      BEDC.Derived.RationalUp.ratOne :=
  normalization.unit_norm

theorem PrimeWindowNormalization.surface_unit_norm
    (normalization : PrimeWindowNormalization) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        (normalization.toUnitaryBalanceSurface).channel)
      BEDC.Derived.RationalUp.ratOne :=
  normalization.unit_norm

theorem PrimeWindowNormalization.den_pos_on_source_window
    (normalization : PrimeWindowNormalization) (p : Nat) :
    normalization.sourceWindow.mem p ->
      0 < normalization.normalizedChannel.amp_den p := by
  intro member
  have normalizedMember : normalization.normalizedChannel.window.mem p := by
    rw [normalization.window_preserved]
    exact member
  exact normalization.normalizedChannel.den_pos p normalizedMember

theorem PrimeWindowNormalization.supported_off_source_window
    (normalization : PrimeWindowNormalization) (p : Nat) :
    Not (normalization.sourceWindow.mem p) ->
      normalization.normalizedChannel.amp_num p = 0 := by
  intro outside
  have outsideNormalized :
      Not (normalization.normalizedChannel.window.mem p) := by
    intro member
    have sourceMember : normalization.sourceWindow.mem p := by
      rw [← normalization.window_preserved]
      exact member
    exact outside sourceMember
  exact normalization.normalizedChannel.supported p outsideNormalized

def normalizeFromUnitaryBalance
    (surface : UnitaryBalanceSurface) : PrimeWindowNormalization where
  sourceWindow := surface.channel.window
  normalizedChannel := surface.channel
  window_preserved := rfl
  unit_norm := surface.norm_one

theorem normalizeFromUnitaryBalance_window
    (surface : UnitaryBalanceSurface) :
    (normalizeFromUnitaryBalance surface).normalizedChannel.window =
      surface.channel.window :=
  rfl

theorem normalizeFromUnitaryBalance_unit_norm
    (surface : UnitaryBalanceSurface) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        (normalizeFromUnitaryBalance surface).normalizedChannel)
      BEDC.Derived.RationalUp.ratOne :=
  surface.norm_one

/--
远端统一归一化把 apophatic socket 与素窗口归一化并列记录。socket 只给边界行;
单位范数仍由素窗口归一化见证传递。
-/
structure FarEndUnityNormalization where
  socket : TranscendentalFarEndSocket
  primeWindow : PrimeWindowNormalization

def FarEndUnityNormalization.toUnitaryBalanceSurface
    (normalization : FarEndUnityNormalization) : UnitaryBalanceSurface :=
  normalization.primeWindow.toUnitaryBalanceSurface

theorem FarEndUnityNormalization.unit_norm_transfers
    (normalization : FarEndUnityNormalization) :
    BEDC.Derived.RationalUp.RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        normalization.toUnitaryBalanceSurface.channel)
      BEDC.Derived.RationalUp.ratOne :=
  normalization.primeWindow.surface_unit_norm

theorem FarEndUnityNormalization.normalized_window
    (normalization : FarEndUnityNormalization) :
    normalization.primeWindow.normalizedChannel.window =
      normalization.primeWindow.sourceWindow :=
  normalization.primeWindow.window_preserved

theorem FarEndUnityNormalization.far_end_not_internalized
    (normalization : FarEndUnityNormalization) :
    BEDC.Derived.TranscendentalFarEndUp.farEndSocketElementProjection
      BEDC.Derived.LocatedReal.RatMetricKitConcrete
      normalization.socket = none :=
  BEDC.Derived.TranscendentalFarEndUp.farEndSocket_no_element_projection
    BEDC.Derived.LocatedReal.RatMetricKitConcrete
    normalization.socket

end BEDC.Derived.RHRoute.FarEndUnityNormalization
