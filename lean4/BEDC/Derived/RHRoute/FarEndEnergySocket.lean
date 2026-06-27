import BEDC.Derived.RHRoute.FarEndUnityNormalization

namespace BEDC.Derived.RHRoute.FarEndEnergySocket

open BEDC.Derived.RationalUp

abbrev TranscendentalFarEndSocket :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.TranscendentalFarEndSocket

abbrev FarEndUnityNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.FarEndUnityNormalization

abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.UnitaryBalanceSurface

abbrev PrimeWindowNormalization :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindowNormalization

abbrev PrimeWindowUnitNorm :=
  BEDC.Derived.RHRoute.FarEndUnityNormalization.PrimeWindowUnitNorm

def UnitEnergy (energy : RatNum) : Prop :=
  RatEq energy ratOne

/--
`energy` 只作路线名中的归一读法: 本文件仅编码 `RatEq energy ratOne`。
socket 仍是 apophatic 边界, 不是 located-process 元素或对象级端点。
-/
structure FarEndEnergyNormalization where
  unity : FarEndUnityNormalization
  energy : RatNum
  energy_unit : UnitEnergy energy

def FarEndEnergyNormalization.socket
    (normalization : FarEndEnergyNormalization) :
    TranscendentalFarEndSocket :=
  normalization.unity.socket

def FarEndEnergyNormalization.toUnitaryBalanceSurface
    (normalization : FarEndEnergyNormalization) :
    UnitaryBalanceSurface :=
  normalization.unity.toUnitaryBalanceSurface

def FarEndEnergyNormalization.primeWindow
    (normalization : FarEndEnergyNormalization) :
    PrimeWindowNormalization :=
  normalization.unity.primeWindow

theorem FarEndEnergyNormalization.energy_is_unit
    (normalization : FarEndEnergyNormalization) :
    UnitEnergy normalization.energy :=
  normalization.energy_unit

theorem FarEndEnergyNormalization.unit_norm_transfers
    (normalization : FarEndEnergyNormalization) :
    RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        normalization.toUnitaryBalanceSurface.channel)
      ratOne :=
  normalization.unity.unit_norm_transfers

theorem FarEndEnergyNormalization.prime_window_unit_norm
    (normalization : FarEndEnergyNormalization) :
    PrimeWindowUnitNorm normalization.primeWindow.normalizedChannel :=
  normalization.unity.primeWindow.unit_norm

theorem FarEndEnergyNormalization.normalized_window
    (normalization : FarEndEnergyNormalization) :
    normalization.primeWindow.normalizedChannel.window =
      normalization.primeWindow.sourceWindow :=
  normalization.unity.normalized_window

theorem FarEndEnergyNormalization.energy_matches_unit_norm
    (normalization : FarEndEnergyNormalization) :
    RatEq normalization.energy
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        normalization.toUnitaryBalanceSurface.channel) :=
  RatEq_trans normalization.energy ratOne
    (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
      normalization.toUnitaryBalanceSurface.channel)
    normalization.energy_unit
    (RatEq_symm normalization.unit_norm_transfers)

theorem FarEndEnergyNormalization.apophatic_socket_not_element
    (normalization : FarEndEnergyNormalization) :
    BEDC.Derived.TranscendentalFarEndUp.farEndSocketElementProjection
      BEDC.Derived.LocatedReal.RatMetricKitConcrete
      normalization.socket = none :=
  normalization.unity.far_end_not_internalized

/--
socket 接口把可读能量归一与远端边界放在同一个有限接口中,
但不增加任何远端元素投影。
-/
structure FarEndEnergySocket where
  normalization : FarEndEnergyNormalization
  socket : TranscendentalFarEndSocket
  toUnitaryBalanceSurface : UnitaryBalanceSurface
  socket_consistent : socket = normalization.unity.socket
  unit_surface_consistent :
    toUnitaryBalanceSurface = normalization.unity.toUnitaryBalanceSurface

def FarEndEnergySocket.energy (socket : FarEndEnergySocket) : RatNum :=
  socket.normalization.energy

def FarEndEnergySocket.unity
    (socket : FarEndEnergySocket) : FarEndUnityNormalization :=
  socket.normalization.unity

def FarEndEnergySocket.primeWindow
    (socket : FarEndEnergySocket) : PrimeWindowNormalization :=
  socket.normalization.primeWindow

def FarEndEnergySocket.fromNormalization
    (normalization : FarEndEnergyNormalization) :
    FarEndEnergySocket where
  normalization := normalization
  socket := normalization.socket
  toUnitaryBalanceSurface := normalization.toUnitaryBalanceSurface
  socket_consistent := rfl
  unit_surface_consistent := rfl

theorem FarEndEnergySocket.energy_unit
    (socket : FarEndEnergySocket) :
    UnitEnergy socket.energy :=
  socket.normalization.energy_is_unit

theorem FarEndEnergySocket.surface_unit_norm
    (socket : FarEndEnergySocket) :
    RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        socket.toUnitaryBalanceSurface.channel)
      ratOne := by
  rw [socket.unit_surface_consistent]
  exact socket.normalization.unit_norm_transfers

theorem FarEndEnergySocket.energy_matches_surface_norm
    (socket : FarEndEnergySocket) :
    RatEq socket.energy
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow
        socket.toUnitaryBalanceSurface.channel) := by
  rw [socket.unit_surface_consistent]
  exact socket.normalization.energy_matches_unit_norm

theorem FarEndEnergySocket.apophatic_socket_not_element
    (socket : FarEndEnergySocket) :
    BEDC.Derived.TranscendentalFarEndUp.farEndSocketElementProjection
      BEDC.Derived.LocatedReal.RatMetricKitConcrete
      socket.socket = none := by
  rw [socket.socket_consistent]
  exact socket.normalization.apophatic_socket_not_element

theorem FarEndEnergySocket.fromNormalization_energy_unit
    (normalization : FarEndEnergyNormalization) :
    UnitEnergy (FarEndEnergySocket.fromNormalization normalization).energy :=
  normalization.energy_unit

theorem FarEndEnergySocket.fromNormalization_no_element
    (normalization : FarEndEnergyNormalization) :
    BEDC.Derived.TranscendentalFarEndUp.farEndSocketElementProjection
      BEDC.Derived.LocatedReal.RatMetricKitConcrete
      (FarEndEnergySocket.fromNormalization normalization).socket = none :=
  normalization.apophatic_socket_not_element

end BEDC.Derived.RHRoute.FarEndEnergySocket
