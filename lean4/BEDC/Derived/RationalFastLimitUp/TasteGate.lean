import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalFastLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalFastLimitUp : Type where
  | mk (Q D S R E H C P N : BHist) : RationalFastLimitUp
  deriving DecidableEq

def rationalFastLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalFastLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalFastLimitEncodeBHist h

def rationalFastLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalFastLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalFastLimitDecodeBHist tail)

private theorem rationalFastLimitDecodeEncode :
    ∀ h : BHist, rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalFastLimitFields : RationalFastLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalFastLimitUp.mk Q D S R E H C P N => [Q, D, S, R, E, H, C, P, N]

def rationalFastLimitToEventFlow : RationalFastLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalFastLimitFields x).map rationalFastLimitEncodeBHist

def rationalFastLimitFromEventFlow : EventFlow → Option RationalFastLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | Q :: D :: S :: R :: E :: H :: C :: P :: N :: [] =>
        some
          (RationalFastLimitUp.mk
            (rationalFastLimitDecodeBHist Q)
            (rationalFastLimitDecodeBHist D)
            (rationalFastLimitDecodeBHist S)
            (rationalFastLimitDecodeBHist R)
            (rationalFastLimitDecodeBHist E)
            (rationalFastLimitDecodeBHist H)
            (rationalFastLimitDecodeBHist C)
            (rationalFastLimitDecodeBHist P)
            (rationalFastLimitDecodeBHist N))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

private theorem rationalFastLimitRoundTrip :
    ∀ x : RationalFastLimitUp,
      rationalFastLimitFromEventFlow (rationalFastLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D S R E H C P N =>
      change
        some
            (RationalFastLimitUp.mk
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist Q))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist D))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist S))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist R))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist E))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist H))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist C))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist P))
              (rationalFastLimitDecodeBHist (rationalFastLimitEncodeBHist N))) =
          some (RationalFastLimitUp.mk Q D S R E H C P N)
      rw [rationalFastLimitDecodeEncode Q, rationalFastLimitDecodeEncode D,
        rationalFastLimitDecodeEncode S, rationalFastLimitDecodeEncode R,
        rationalFastLimitDecodeEncode E, rationalFastLimitDecodeEncode H,
        rationalFastLimitDecodeEncode C, rationalFastLimitDecodeEncode P,
        rationalFastLimitDecodeEncode N]

private theorem rationalFastLimitToEventFlow_injective {x y : RationalFastLimitUp} :
    rationalFastLimitToEventFlow x = rationalFastLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalFastLimitFromEventFlow (rationalFastLimitToEventFlow x) =
        rationalFastLimitFromEventFlow (rationalFastLimitToEventFlow y) :=
    congrArg rationalFastLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalFastLimitRoundTrip x).symm
      (Eq.trans hread (rationalFastLimitRoundTrip y)))

def rationalFastLimitCarrier : BHistCarrier RationalFastLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalFastLimitToEventFlow
  fromEventFlow := rationalFastLimitFromEventFlow

instance rationalFastLimitBHistCarrier : BHistCarrier RationalFastLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalFastLimitCarrier

def rationalFastLimitGate : @ChapterTasteGate RationalFastLimitUp rationalFastLimitCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalFastLimitFromEventFlow (rationalFastLimitToEventFlow x) = some x
    exact rationalFastLimitRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalFastLimitToEventFlow_injective heq)

instance rationalFastLimitChapterTasteGate : ChapterTasteGate RationalFastLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalFastLimitGate

theorem RationalFastLimitTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RationalFastLimitUp) ∧
      Nonempty (ChapterTasteGate RationalFastLimitUp) ∧
        rationalFastLimitFields
            (RationalFastLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨rationalFastLimitCarrier⟩, ⟨rationalFastLimitGate⟩, rfl⟩

end BEDC.Derived.RationalFastLimitUp
