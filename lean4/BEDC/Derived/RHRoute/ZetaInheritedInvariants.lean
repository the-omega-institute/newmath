import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.PrimeSkewDefect
import BEDC.Derived.RHRoute.UnitaryBalance
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.RHRoute.ZetaInheritedInvariants

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.UnitaryBalance

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev PrimeLocalChannel :=
  BEDC.Derived.RHRoute.UnitaryBalance.PrimeLocalChannel

abbrev UnitaryBalanceSurface :=
  BEDC.Derived.RHRoute.UnitaryBalance.UnitaryBalanceSurface

abbrev RatComplex :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.RatComplex

abbrev OnCriticalLine :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.OnCriticalLine

abbrev BoxGauge :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.BoxGauge

abbrev CriticalStripInput :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.CriticalStripInput

abbrev ZetaBoxEvaluator :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaBoxEvaluator

abbrev ZetaPrecisionPacket {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) (k : Nat) :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ZetaPrecisionPacket E k

-- 尺度归一化在本地素数通道里读作分母正性, 不引入独立解析对象。
def CenteredChannelScaleNormalized (C : PrimeLocalChannel) : Prop :=
  (p : Nat) -> C.window.mem p -> 0 < C.amp_den p

-- 频率与对数素数钟只记录有限窗口上的可读编号。
structure PrimeClockTransfer where
  window : PrimeWindow
  fourierFrequency : Nat -> Nat

def logPrimeClock (transfer : PrimeClockTransfer) (p : Nat) : Nat :=
  transfer.fourierFrequency p

structure ZetaConstructionChain (G : BoxGauge) (s : CriticalStripInput) where
  evaluator : ZetaBoxEvaluator G s
  centeredChannel : PrimeLocalChannel
  balanceSurface : UnitaryBalanceSurface
  balance_channel_eq : balanceSurface.channel = centeredChannel
  criticalPoint : RatComplex
  criticalLineReadback : OnCriticalLine criticalPoint
  clocks : PrimeClockTransfer
  clocks_window_eq : clocks.window.elems = centeredChannel.window.elems

theorem scaleNormalization_to_centeredPrimeChannel
    (C : PrimeLocalChannel) :
    CenteredChannelScaleNormalized C := by
  intro p member
  exact C.den_pos p member

theorem centeredPrimeChannel_amplitude_reads_unitary
    (C : PrimeLocalChannel) (p : Nat) :
    BEDC.Derived.RHRoute.PrimeSkewDefect.centeredUnitaryAmplitude C p =
      channelAmplitude C p := by
  rfl

theorem unitNorm_on_centeredChannel
    {G : BoxGauge} {s : CriticalStripInput}
    (chain : ZetaConstructionChain G s) :
    RatEq (squaredNormOnWindow chain.centeredChannel) ratOne := by
  rw [← chain.balance_channel_eq]
  exact chain.balanceSurface.norm_one

theorem unitNorm_transfers_to_criticalLine
    {G : BoxGauge} {s : CriticalStripInput}
    (chain : ZetaConstructionChain G s) :
    RatEq (squaredNormOnWindow chain.centeredChannel) ratOne ∧
      OnCriticalLine chain.criticalPoint := by
  exact And.intro (unitNorm_on_centeredChannel chain)
    chain.criticalLineReadback

theorem criticalLine_reads_re_half
    {G : BoxGauge} {s : CriticalStripInput}
    (chain : ZetaConstructionChain G s) :
    OnCriticalLine chain.criticalPoint =
      RatEq chain.criticalPoint.re
        BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat := by
  exact
    BEDC.Derived.RHRoute.ConstructiveRHStatement.onCriticalLine_reads_re_half
      chain.criticalPoint

theorem fourierFrequency_to_logPrimeClock
    (transfer : PrimeClockTransfer) (p : Nat)
    (_member : transfer.window.mem p) :
    logPrimeClock transfer p = transfer.fourierFrequency p := by
  rfl

theorem logPrimeClock_source_is_prime
    (transfer : PrimeClockTransfer) (p : Nat)
    (member : transfer.window.mem p) :
    IsPrime p := by
  exact All.mem transfer.window.all_prime member

theorem chain_scaleNormalization_to_centeredPrimeChannel
    {G : BoxGauge} {s : CriticalStripInput}
    (chain : ZetaConstructionChain G s) :
    CenteredChannelScaleNormalized chain.centeredChannel := by
  exact scaleNormalization_to_centeredPrimeChannel chain.centeredChannel

theorem chain_fourierFrequency_to_logPrimeClock
    {G : BoxGauge} {s : CriticalStripInput}
    (chain : ZetaConstructionChain G s) (p : Nat)
    (member : chain.clocks.window.mem p) :
    logPrimeClock chain.clocks p = chain.clocks.fourierFrequency p := by
  exact fourierFrequency_to_logPrimeClock chain.clocks p member

theorem chain_logPrimeClock_source_is_prime
    {G : BoxGauge} {s : CriticalStripInput}
    (chain : ZetaConstructionChain G s) (p : Nat)
    (member : chain.clocks.window.mem p) :
    IsPrime p := by
  exact logPrimeClock_source_is_prime chain.clocks p member

theorem chain_zetaBox_precision_packet
    {G : BoxGauge} {s : CriticalStripInput}
    (chain : ZetaConstructionChain G s) (k : Nat) :
    ∃ packet : ZetaPrecisionPacket chain.evaluator k,
      G.fits packet.zetaBox k := by
  exact
    BEDC.Derived.RHRoute.ZetaBoxEvaluator.zetaBoxEvaluableToPrecision
      chain.evaluator k

end BEDC.Derived.RHRoute.ZetaInheritedInvariants
