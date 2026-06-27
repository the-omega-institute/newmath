import BEDC.Derived.RegularCauchyApartnessReflectorUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

structure RegularCauchyApartnessReflectorEventFlow where
  rows : List BHist

def regularCauchyApartnessReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyApartnessReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyApartnessReflectorEncodeBHist h

def regularCauchyApartnessReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyApartnessReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyApartnessReflectorDecodeBHist tail)

private theorem RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyApartnessReflectorDecodeBHist
        (regularCauchyApartnessReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyApartnessReflectorFields :
    RegularCauchyApartnessReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyApartnessReflectorUp.mk S R D A L E H C N => [S, R, D, A, L, E, H, C, N]

def regularCauchyApartnessReflectorToEventFlow
    (x : RegularCauchyApartnessReflectorUp) :
    RegularCauchyApartnessReflectorEventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  ⟨regularCauchyApartnessReflectorFields x⟩

def regularCauchyApartnessReflectorToGroundEventFlow :
    RegularCauchyApartnessReflectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyApartnessReflectorFields x).map
      regularCauchyApartnessReflectorEncodeBHist

def regularCauchyApartnessReflectorFromGroundEventFlow
    (ef : EventFlow) : Option RegularCauchyApartnessReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | S :: R :: D :: A :: L :: E :: H :: C :: N :: [] =>
      some
        (RegularCauchyApartnessReflectorUp.mk
          (regularCauchyApartnessReflectorDecodeBHist S)
          (regularCauchyApartnessReflectorDecodeBHist R)
          (regularCauchyApartnessReflectorDecodeBHist D)
          (regularCauchyApartnessReflectorDecodeBHist A)
          (regularCauchyApartnessReflectorDecodeBHist L)
          (regularCauchyApartnessReflectorDecodeBHist E)
          (regularCauchyApartnessReflectorDecodeBHist H)
          (regularCauchyApartnessReflectorDecodeBHist C)
          (regularCauchyApartnessReflectorDecodeBHist N))
  | _ => none

private theorem RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyApartnessReflectorUp) :
    regularCauchyApartnessReflectorFromGroundEventFlow
      (regularCauchyApartnessReflectorToGroundEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S R D A L E H C N =>
      change
        some
          (RegularCauchyApartnessReflectorUp.mk
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist S))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist R))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist D))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist A))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist L))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist E))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist H))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist C))
            (regularCauchyApartnessReflectorDecodeBHist
              (regularCauchyApartnessReflectorEncodeBHist N))) =
          some (RegularCauchyApartnessReflectorUp.mk S R D A L E H C N)
      rw [RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyApartnessReflectorUp} :
    regularCauchyApartnessReflectorToGroundEventFlow x =
        regularCauchyApartnessReflectorToGroundEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyApartnessReflectorFromGroundEventFlow
          (regularCauchyApartnessReflectorToGroundEventFlow x) =
        regularCauchyApartnessReflectorFromGroundEventFlow
          (regularCauchyApartnessReflectorToGroundEventFlow y) :=
    congrArg regularCauchyApartnessReflectorFromGroundEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyApartnessReflectorBHistCarrier :
    BHistCarrier RegularCauchyApartnessReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyApartnessReflectorToGroundEventFlow
  fromEventFlow := regularCauchyApartnessReflectorFromGroundEventFlow

instance regularCauchyApartnessReflectorChapterTasteGate :
    ChapterTasteGate RegularCauchyApartnessReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyApartnessReflectorFromGroundEventFlow
        (regularCauchyApartnessReflectorToGroundEventFlow x) = some x
    exact RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyApartnessReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyApartnessReflectorChapterTasteGate

theorem RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyApartnessReflectorDecodeBHist
          (regularCauchyApartnessReflectorEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyApartnessReflectorUp,
        (regularCauchyApartnessReflectorToEventFlow x).rows =
          regularCauchyApartnessReflectorFields x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyApartnessReflectorTasteGate_single_carrier_alignment_decode_encode,
      fun x => rfl⟩

end BEDC.Derived.RegularCauchyApartnessReflectorUp
