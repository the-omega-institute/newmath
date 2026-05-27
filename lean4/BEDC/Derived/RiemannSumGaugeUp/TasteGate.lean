import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannSumGaugeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannSumGaugeUp : Type where
  | mk (I T Q M D W R E H C P N : BHist) : RiemannSumGaugeUp
  deriving DecidableEq

def riemannSumGaugeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannSumGaugeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannSumGaugeEncodeBHist h

def riemannSumGaugeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannSumGaugeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannSumGaugeDecodeBHist tail)

private theorem RiemannSumGaugeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannSumGaugeFields : RiemannSumGaugeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannSumGaugeUp.mk I T Q M D W R E H C P N => [I, T, Q, M, D, W, R, E, H, C, P, N]

def riemannSumGaugeToEventFlow : RiemannSumGaugeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannSumGaugeFields x).map riemannSumGaugeEncodeBHist

def riemannSumGaugeFromEventFlow : EventFlow → Option RiemannSumGaugeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _I :: [] => none
  | _I :: _T :: [] => none
  | _I :: _T :: _Q :: [] => none
  | _I :: _T :: _Q :: _M :: [] => none
  | _I :: _T :: _Q :: _M :: _D :: [] => none
  | _I :: _T :: _Q :: _M :: _D :: _W :: [] => none
  | _I :: _T :: _Q :: _M :: _D :: _W :: _R :: [] => none
  | _I :: _T :: _Q :: _M :: _D :: _W :: _R :: _E :: [] => none
  | _I :: _T :: _Q :: _M :: _D :: _W :: _R :: _E :: _H :: [] => none
  | _I :: _T :: _Q :: _M :: _D :: _W :: _R :: _E :: _H :: _C :: [] => none
  | _I :: _T :: _Q :: _M :: _D :: _W :: _R :: _E :: _H :: _C :: _P :: [] => none
  | I :: T :: Q :: M :: D :: W :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (RiemannSumGaugeUp.mk
          (riemannSumGaugeDecodeBHist I)
          (riemannSumGaugeDecodeBHist T)
          (riemannSumGaugeDecodeBHist Q)
          (riemannSumGaugeDecodeBHist M)
          (riemannSumGaugeDecodeBHist D)
          (riemannSumGaugeDecodeBHist W)
          (riemannSumGaugeDecodeBHist R)
          (riemannSumGaugeDecodeBHist E)
          (riemannSumGaugeDecodeBHist H)
          (riemannSumGaugeDecodeBHist C)
          (riemannSumGaugeDecodeBHist P)
          (riemannSumGaugeDecodeBHist N))
  | _I :: _T :: _Q :: _M :: _D :: _W :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem RiemannSumGaugeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannSumGaugeUp,
      riemannSumGaugeFromEventFlow (riemannSumGaugeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I T Q M D W R E H C P N =>
      change
        some
          (RiemannSumGaugeUp.mk
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist I))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist T))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist Q))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist M))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist D))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist W))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist R))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist E))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist H))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist C))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist P))
            (riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist N))) =
          some (RiemannSumGaugeUp.mk I T Q M D W R E H C P N)
      rw [RiemannSumGaugeTasteGate_single_carrier_alignment_decode I,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode T,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode Q,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode M,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode D,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode W,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode R,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode E,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode H,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode C,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode P,
        RiemannSumGaugeTasteGate_single_carrier_alignment_decode N]

private theorem RiemannSumGaugeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannSumGaugeUp} :
    riemannSumGaugeToEventFlow x = riemannSumGaugeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannSumGaugeFromEventFlow (riemannSumGaugeToEventFlow x) =
        riemannSumGaugeFromEventFlow (riemannSumGaugeToEventFlow y) :=
    congrArg riemannSumGaugeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannSumGaugeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RiemannSumGaugeTasteGate_single_carrier_alignment_round_trip y)))

private theorem RiemannSumGaugeTasteGate_single_carrier_alignment_fields :
    ∀ x y : RiemannSumGaugeUp, riemannSumGaugeFields x = riemannSumGaugeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 T1 Q1 M1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 T2 Q2 M2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance riemannSumGaugeBHistCarrier : BHistCarrier RiemannSumGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannSumGaugeToEventFlow
  fromEventFlow := riemannSumGaugeFromEventFlow

instance riemannSumGaugeChapterTasteGate : ChapterTasteGate RiemannSumGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannSumGaugeFromEventFlow (riemannSumGaugeToEventFlow x) = some x
    exact RiemannSumGaugeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannSumGaugeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance riemannSumGaugeFieldFaithful : FieldFaithful RiemannSumGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannSumGaugeFields
  field_faithful := RiemannSumGaugeTasteGate_single_carrier_alignment_fields

instance riemannSumGaugeNontrivial : Nontrivial RiemannSumGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannSumGaugeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RiemannSumGaugeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RiemannSumGaugeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannSumGaugeChapterTasteGate

theorem RiemannSumGaugeTasteGate_single_carrier_alignment :
    (∀ h : BHist, riemannSumGaugeDecodeBHist (riemannSumGaugeEncodeBHist h) = h) ∧
      (∀ x : RiemannSumGaugeUp,
        riemannSumGaugeFromEventFlow (riemannSumGaugeToEventFlow x) = some x) ∧
        (∀ x y : RiemannSumGaugeUp,
          riemannSumGaugeToEventFlow x = riemannSumGaugeToEventFlow y → x = y) ∧
          riemannSumGaugeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RiemannSumGaugeTasteGate_single_carrier_alignment_decode,
      RiemannSumGaugeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RiemannSumGaugeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RiemannSumGaugeUp
