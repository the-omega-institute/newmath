import BEDC.Derived.RHRoute.EventflowCertificate
import BEDC.Derived.RHRoute.UnitaryBalance

namespace BEDC.Derived.RHRoute.PrimeSkewDefect

open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.UnitaryBalance
open BEDC.Derived.RationalUp

universe u v

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow
abbrev PrimeLocalChannel := BEDC.Derived.RHRoute.UnitaryBalance.PrimeLocalChannel
abbrev RatNum := BEDC.Derived.RationalUp.RatNum

def centeredUnitaryAmplitude (C : PrimeLocalChannel) (p : Nat) : RatNum :=
  channelAmplitude C p

def amplitudeDeviationFromOne (C : PrimeLocalChannel) (p : Nat) : RatNum :=
  ratAdd (centeredUnitaryAmplitude C p) (ratNeg ratOne)

def rawAmplitudeDiffersFromOne (C : PrimeLocalChannel) (p : Nat) : Bool :=
  if C.amp_num p = Int.ofNat (C.amp_den p) then false else true

theorem rawAmplitudeDiffersFromOne_true_ne
    (C : PrimeLocalChannel) (p : Nat) :
    rawAmplitudeDiffersFromOne C p = true ->
      C.amp_num p ≠ Int.ofNat (C.amp_den p) := by
  intro checked same
  unfold rawAmplitudeDiffersFromOne at checked
  rw [if_pos same] at checked
  cases checked

structure MirrorPrimeChannels where
  source : PrimeLocalChannel
  mirror : PrimeLocalChannel
  same_window : mirror.window.elems = source.window.elems

def mirrorAmplitudeSkew (channels : MirrorPrimeChannels) (p : Nat) : RatNum :=
  ratAdd (centeredUnitaryAmplitude channels.mirror p)
    (ratNeg (centeredUnitaryAmplitude channels.source p))

def rawMirrorSkewCheck (channels : MirrorPrimeChannels) (p : Nat) : Bool :=
  if channels.source.amp_num p * Int.ofNat (channels.mirror.amp_den p) =
      channels.mirror.amp_num p * Int.ofNat (channels.source.amp_den p) then
    false
  else
    true

theorem rawMirrorSkewCheck_true_ne
    (channels : MirrorPrimeChannels) (p : Nat) :
    rawMirrorSkewCheck channels p = true ->
      channels.source.amp_num p * Int.ofNat (channels.mirror.amp_den p) ≠
        channels.mirror.amp_num p * Int.ofNat (channels.source.amp_den p) := by
  intro checked same
  unfold rawMirrorSkewCheck at checked
  rw [if_pos same] at checked
  cases checked

structure PrimeSkewCertificate (channels : MirrorPrimeChannels) where
  prime : Nat
  source_mem : channels.source.window.mem prime
  mirror_mem : channels.mirror.window.mem prime
  source_deviates_from_one :
    rawAmplitudeDiffersFromOne channels.source prime = true
  mirror_deviates_from_one :
    rawAmplitudeDiffersFromOne channels.mirror prime = true
  mirror_skew_checked :
    rawMirrorSkewCheck channels prime = true

namespace PrimeSkewCertificate

def sourceAmplitude {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) : RatNum :=
  centeredUnitaryAmplitude channels.source cert.prime

def mirrorAmplitude {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) : RatNum :=
  centeredUnitaryAmplitude channels.mirror cert.prime

def sourceDeviation {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) : RatNum :=
  amplitudeDeviationFromOne channels.source cert.prime

def mirrorSkew {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) : RatNum :=
  mirrorAmplitudeSkew channels cert.prime

theorem source_prime {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    IsPrime cert.prime := by
  exact All.mem channels.source.window.all_prime cert.source_mem

theorem source_deviation_raw_apart {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    channels.source.amp_num cert.prime ≠
      Int.ofNat (channels.source.amp_den cert.prime) := by
  exact rawAmplitudeDiffersFromOne_true_ne channels.source cert.prime
    cert.source_deviates_from_one

theorem mirror_deviation_raw_apart {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    channels.mirror.amp_num cert.prime ≠
      Int.ofNat (channels.mirror.amp_den cert.prime) := by
  exact rawAmplitudeDiffersFromOne_true_ne channels.mirror cert.prime
    cert.mirror_deviates_from_one

theorem mirror_skew_raw_apart {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    channels.source.amp_num cert.prime *
        Int.ofNat (channels.mirror.amp_den cert.prime) ≠
      channels.mirror.amp_num cert.prime *
        Int.ofNat (channels.source.amp_den cert.prime) := by
  exact rawMirrorSkewCheck_true_ne channels cert.prime cert.mirror_skew_checked

theorem sourceDeviation_is_quantized {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    RatEq cert.sourceDeviation
      (amplitudeDeviationFromOne channels.source cert.prime) := by
  exact RatEq_refl _

theorem mirrorSkew_is_quantized {channels : MirrorPrimeChannels}
    (cert : PrimeSkewCertificate channels) :
    RatEq cert.mirrorSkew (mirrorAmplitudeSkew channels cert.prime) := by
  exact RatEq_refl _

end PrimeSkewCertificate

structure PrimeDefectRow where
  layer : Nat
  prime : Nat
  defect_quantum : RatNum
  defect_apart_zero : ratApart0 defect_quantum

structure PrimeDefect (Bulk : Type u) (x : Bulk) where
  rows : List PrimeDefectRow
  selected : PrimeDefectRow
  selected_mem : selected ∈ rows

theorem prime_defect_selected_mem {Bulk : Type u} {x : Bulk}
    (defect : PrimeDefect Bulk x) :
    defect.selected ∈ defect.rows := by
  exact defect.selected_mem

structure PrimeSkewDefectInterface where
  bulk : Type u
  zero_atom : bulk -> Type v
  channels : bulk -> MirrorPrimeChannels

structure BoundaryFaithfulness (I : PrimeSkewDefectInterface) where
  detects :
    (x : I.bulk) ->
      I.zero_atom x ->
        PrimeSkewCertificate (I.channels x) ->
          PrimeDefect I.bulk x

def PrimeDefectZeroIncompatibility
    (I : PrimeSkewDefectInterface) : Prop :=
  (x : I.bulk) ->
    I.zero_atom x ->
      PrimeDefect I.bulk x ->
        False

structure LocatedPrimeSkewCertificate
    (I : PrimeSkewDefectInterface) where
  point : I.bulk
  zero : I.zero_atom point
  skew : PrimeSkewCertificate (I.channels point)

theorem skew_certificate_refutes_faithfulness
    {I : PrimeSkewDefectInterface}
    (cert : LocatedPrimeSkewCertificate I)
    (incompatible : PrimeDefectZeroIncompatibility I) :
    BoundaryFaithfulness I -> False := by
  intro faithful
  exact incompatible cert.point cert.zero
    (faithful.detects cert.point cert.zero cert.skew)

structure OffLineZeroBoundaryObligation
    (I : PrimeSkewDefectInterface) where
  off_line_zero : Type v
  locate : off_line_zero -> I.bulk
  zero_atom_at : (z : off_line_zero) -> I.zero_atom (locate z)
  off_line_to_prime_skew_boundary_obligation :
    (z : off_line_zero) -> PrimeSkewCertificate (I.channels (locate z))

def boundary_obligation_to_located_skew
    {I : PrimeSkewDefectInterface}
    (obligation : OffLineZeroBoundaryObligation I)
    (z : obligation.off_line_zero) :
    LocatedPrimeSkewCertificate I where
  point := obligation.locate z
  zero := obligation.zero_atom_at z
  skew := obligation.off_line_to_prime_skew_boundary_obligation z

theorem boundary_obligation_refutes_faithfulness_conditionally
    {I : PrimeSkewDefectInterface}
    (obligation : OffLineZeroBoundaryObligation I)
    (incompatible : PrimeDefectZeroIncompatibility I)
    (z : obligation.off_line_zero) :
    BoundaryFaithfulness I -> False := by
  exact skew_certificate_refutes_faithfulness
    (boundary_obligation_to_located_skew obligation z) incompatible

end BEDC.Derived.RHRoute.PrimeSkewDefect
