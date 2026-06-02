import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractiveCauchyOrbitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractiveCauchyOrbitUp : Type where
  | mk (X T I W R M K E H C P N : BHist) : ContractiveCauchyOrbitUp
  deriving DecidableEq

def contractiveCauchyOrbitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractiveCauchyOrbitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractiveCauchyOrbitEncodeBHist h

def contractiveCauchyOrbitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractiveCauchyOrbitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractiveCauchyOrbitDecodeBHist tail)

private theorem contractiveCauchyOrbitDecode_encode_bhist :
    ∀ h : BHist, contractiveCauchyOrbitDecodeBHist
      (contractiveCauchyOrbitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractiveCauchyOrbitFields : ContractiveCauchyOrbitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractiveCauchyOrbitUp.mk X T I W R M K E H C P N =>
      [X, T, I, W, R, M, K, E, H, C, P, N]

def contractiveCauchyOrbitToEventFlow : ContractiveCauchyOrbitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contractiveCauchyOrbitFields x).map contractiveCauchyOrbitEncodeBHist

private def contractiveCauchyOrbitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contractiveCauchyOrbitEventAtDefault index rest

def contractiveCauchyOrbitFromEventFlow : EventFlow → Option ContractiveCauchyOrbitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ContractiveCauchyOrbitUp.mk
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 0 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 1 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 2 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 3 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 4 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 5 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 6 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 7 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 8 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 9 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 10 ef))
        (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEventAtDefault 11 ef)))

private theorem contractiveCauchyOrbit_round_trip :
    ∀ x : ContractiveCauchyOrbitUp,
      contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T I W R M K E H C P N =>
      change
        some
          (ContractiveCauchyOrbitUp.mk
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist X))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist T))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist I))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist W))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist R))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist M))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist K))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist E))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist H))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist C))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist P))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist N))) =
          some (ContractiveCauchyOrbitUp.mk X T I W R M K E H C P N)
      rw [contractiveCauchyOrbitDecode_encode_bhist X,
        contractiveCauchyOrbitDecode_encode_bhist T,
        contractiveCauchyOrbitDecode_encode_bhist I,
        contractiveCauchyOrbitDecode_encode_bhist W,
        contractiveCauchyOrbitDecode_encode_bhist R,
        contractiveCauchyOrbitDecode_encode_bhist M,
        contractiveCauchyOrbitDecode_encode_bhist K,
        contractiveCauchyOrbitDecode_encode_bhist E,
        contractiveCauchyOrbitDecode_encode_bhist H,
        contractiveCauchyOrbitDecode_encode_bhist C,
        contractiveCauchyOrbitDecode_encode_bhist P,
        contractiveCauchyOrbitDecode_encode_bhist N]

private theorem contractiveCauchyOrbitToEventFlow_injective
    {x y : ContractiveCauchyOrbitUp} :
    contractiveCauchyOrbitToEventFlow x = contractiveCauchyOrbitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
        contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow y) :=
    congrArg contractiveCauchyOrbitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (contractiveCauchyOrbit_round_trip x).symm
      (Eq.trans hread (contractiveCauchyOrbit_round_trip y)))

instance contractiveCauchyOrbitBHistCarrier : BHistCarrier ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractiveCauchyOrbitToEventFlow
  fromEventFlow := contractiveCauchyOrbitFromEventFlow

instance contractiveCauchyOrbitChapterTasteGate :
    ChapterTasteGate ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
        some x
    exact contractiveCauchyOrbit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contractiveCauchyOrbitToEventFlow_injective heq)

theorem ContractiveCauchyOrbitTasteGate_single_carrier_alignment :
    (∀ h : BHist, contractiveCauchyOrbitDecodeBHist
      (contractiveCauchyOrbitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ContractiveCauchyOrbitUp) ∧
        Nonempty (ChapterTasteGate ContractiveCauchyOrbitUp) ∧
          contractiveCauchyOrbitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact contractiveCauchyOrbitDecode_encode_bhist
  · constructor
    · exact ⟨contractiveCauchyOrbitBHistCarrier⟩
    · constructor
      · exact ⟨contractiveCauchyOrbitChapterTasteGate⟩
      · rfl

end BEDC.Derived.ContractiveCauchyOrbitUp
