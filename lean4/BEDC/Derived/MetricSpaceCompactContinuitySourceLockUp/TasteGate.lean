import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricSpaceCompactContinuitySourceLockUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricSpaceCompactContinuitySourceLockUp : Type where
  | mk : (M K F P R H C N : BHist) → MetricSpaceCompactContinuitySourceLockUp
  deriving DecidableEq

def metricSpaceCompactContinuitySourceLockEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricSpaceCompactContinuitySourceLockEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricSpaceCompactContinuitySourceLockEncodeBHist h

def metricSpaceCompactContinuitySourceLockDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricSpaceCompactContinuitySourceLockDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricSpaceCompactContinuitySourceLockDecodeBHist tail)

private theorem metricSpaceCompactContinuitySourceLockDecode_encode_bhist :
    ∀ h : BHist,
      metricSpaceCompactContinuitySourceLockDecodeBHist
        (metricSpaceCompactContinuitySourceLockEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def metricSpaceCompactContinuitySourceLockFields :
    MetricSpaceCompactContinuitySourceLockUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricSpaceCompactContinuitySourceLockUp.mk M K F P R H C N =>
      [M, K, F, P, R, H, C, N]

def metricSpaceCompactContinuitySourceLockToEventFlow :
    MetricSpaceCompactContinuitySourceLockUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metricSpaceCompactContinuitySourceLockFields x).map
        metricSpaceCompactContinuitySourceLockEncodeBHist

def metricSpaceCompactContinuitySourceLockFromEventFlow :
    EventFlow → Option MetricSpaceCompactContinuitySourceLockUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _M :: [] => none
  | _M :: _K :: [] => none
  | _M :: _K :: _F :: [] => none
  | _M :: _K :: _F :: _P :: [] => none
  | _M :: _K :: _F :: _P :: _R :: [] => none
  | _M :: _K :: _F :: _P :: _R :: _H :: [] => none
  | _M :: _K :: _F :: _P :: _R :: _H :: _C :: [] => none
  | M :: K :: F :: P :: R :: H :: C :: N :: [] =>
      some
        (MetricSpaceCompactContinuitySourceLockUp.mk
          (metricSpaceCompactContinuitySourceLockDecodeBHist M)
          (metricSpaceCompactContinuitySourceLockDecodeBHist K)
          (metricSpaceCompactContinuitySourceLockDecodeBHist F)
          (metricSpaceCompactContinuitySourceLockDecodeBHist P)
          (metricSpaceCompactContinuitySourceLockDecodeBHist R)
          (metricSpaceCompactContinuitySourceLockDecodeBHist H)
          (metricSpaceCompactContinuitySourceLockDecodeBHist C)
          (metricSpaceCompactContinuitySourceLockDecodeBHist N))
  | _M :: _K :: _F :: _P :: _R :: _H :: _C :: _N :: _extra :: _rest => none

private theorem metricSpaceCompactContinuitySourceLock_mk_congr
    {M M' K K' F F' P P' R R' H H' C C' N N' : BHist}
    (hM : M' = M) (hK : K' = K) (hF : F' = F) (hP : P' = P)
    (hR : R' = R) (hH : H' = H) (hC : C' = C) (hN : N' = N) :
    MetricSpaceCompactContinuitySourceLockUp.mk M' K' F' P' R' H' C' N' =
      MetricSpaceCompactContinuitySourceLockUp.mk M K F P R H C N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hK
  cases hF
  cases hP
  cases hR
  cases hH
  cases hC
  cases hN
  rfl

private theorem metricSpaceCompactContinuitySourceLock_round_trip :
    ∀ x : MetricSpaceCompactContinuitySourceLockUp,
      metricSpaceCompactContinuitySourceLockFromEventFlow
        (metricSpaceCompactContinuitySourceLockToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K F P R H C N =>
      exact
        congrArg some
          (metricSpaceCompactContinuitySourceLock_mk_congr
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist M)
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist K)
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist F)
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist P)
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist R)
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist H)
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist C)
            (metricSpaceCompactContinuitySourceLockDecode_encode_bhist N))

private theorem metricSpaceCompactContinuitySourceLockToEventFlow_injective
    {x y : MetricSpaceCompactContinuitySourceLockUp} :
    metricSpaceCompactContinuitySourceLockToEventFlow x =
      metricSpaceCompactContinuitySourceLockToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricSpaceCompactContinuitySourceLockFromEventFlow
          (metricSpaceCompactContinuitySourceLockToEventFlow x) =
        metricSpaceCompactContinuitySourceLockFromEventFlow
          (metricSpaceCompactContinuitySourceLockToEventFlow y) :=
    congrArg metricSpaceCompactContinuitySourceLockFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricSpaceCompactContinuitySourceLock_round_trip x).symm
      (Eq.trans hread (metricSpaceCompactContinuitySourceLock_round_trip y)))

private theorem metricSpaceCompactContinuitySourceLock_field_faithful :
    ∀ x y : MetricSpaceCompactContinuitySourceLockUp,
      metricSpaceCompactContinuitySourceLockFields x =
        metricSpaceCompactContinuitySourceLockFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M K F P R H C N =>
      cases y with
      | mk M' K' F' P' R' H' C' N' =>
          cases hfields
          rfl

instance metricSpaceCompactContinuitySourceLockBHistCarrier :
    BHistCarrier MetricSpaceCompactContinuitySourceLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricSpaceCompactContinuitySourceLockToEventFlow
  fromEventFlow := metricSpaceCompactContinuitySourceLockFromEventFlow

instance metricSpaceCompactContinuitySourceLockChapterTasteGate :
    ChapterTasteGate MetricSpaceCompactContinuitySourceLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricSpaceCompactContinuitySourceLockFromEventFlow
        (metricSpaceCompactContinuitySourceLockToEventFlow x) = some x
    exact metricSpaceCompactContinuitySourceLock_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricSpaceCompactContinuitySourceLockToEventFlow_injective heq)

instance metricSpaceCompactContinuitySourceLockFieldFaithful :
    FieldFaithful MetricSpaceCompactContinuitySourceLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricSpaceCompactContinuitySourceLockFields
  field_faithful := metricSpaceCompactContinuitySourceLock_field_faithful

instance metricSpaceCompactContinuitySourceLockNontrivial :
    Nontrivial MetricSpaceCompactContinuitySourceLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricSpaceCompactContinuitySourceLockUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricSpaceCompactContinuitySourceLockUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricSpaceCompactContinuitySourceLockUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricSpaceCompactContinuitySourceLockChapterTasteGate

theorem MetricSpaceCompactContinuitySourceLockTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricSpaceCompactContinuitySourceLockDecodeBHist
        (metricSpaceCompactContinuitySourceLockEncodeBHist h) = h) ∧
      Nonempty (Nontrivial MetricSpaceCompactContinuitySourceLockUp) ∧
        Nonempty (ChapterTasteGate MetricSpaceCompactContinuitySourceLockUp) ∧
          Nonempty (FieldFaithful MetricSpaceCompactContinuitySourceLockUp) ∧
            metricSpaceCompactContinuitySourceLockEncodeBHist BHist.Empty =
              ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨metricSpaceCompactContinuitySourceLockDecode_encode_bhist,
      ⟨metricSpaceCompactContinuitySourceLockNontrivial⟩,
      ⟨metricSpaceCompactContinuitySourceLockChapterTasteGate⟩,
      ⟨metricSpaceCompactContinuitySourceLockFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.MetricSpaceCompactContinuitySourceLockUp
