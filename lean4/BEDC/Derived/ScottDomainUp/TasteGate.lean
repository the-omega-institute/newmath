import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScottDomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScottDomainUp : Type where
  | mk (O S U B A V R H C P N : BHist) : ScottDomainUp
  deriving DecidableEq

def scottDomainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: scottDomainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: scottDomainEncodeBHist h

def scottDomainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (scottDomainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (scottDomainDecodeBHist tail)

theorem ScottDomainTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, scottDomainDecodeBHist (scottDomainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def scottDomainFields : ScottDomainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScottDomainUp.mk O S U B A V R H C P N => [O, S, U, B, A, V, R, H, C, P, N]

def scottDomainToEventFlow : ScottDomainUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (scottDomainFields x).map scottDomainEncodeBHist

def scottDomainFromEventFlow : EventFlow → Option ScottDomainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | O :: S :: U :: B :: A :: V :: R :: H :: C :: P :: N :: [] =>
      some
        (ScottDomainUp.mk
          (scottDomainDecodeBHist O)
          (scottDomainDecodeBHist S)
          (scottDomainDecodeBHist U)
          (scottDomainDecodeBHist B)
          (scottDomainDecodeBHist A)
          (scottDomainDecodeBHist V)
          (scottDomainDecodeBHist R)
          (scottDomainDecodeBHist H)
          (scottDomainDecodeBHist C)
          (scottDomainDecodeBHist P)
          (scottDomainDecodeBHist N))
  | _ => none

private theorem ScottDomainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ScottDomainUp,
      scottDomainFromEventFlow (scottDomainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O S U B A V R H C P N =>
      change
        some
          (ScottDomainUp.mk
            (scottDomainDecodeBHist (scottDomainEncodeBHist O))
            (scottDomainDecodeBHist (scottDomainEncodeBHist S))
            (scottDomainDecodeBHist (scottDomainEncodeBHist U))
            (scottDomainDecodeBHist (scottDomainEncodeBHist B))
            (scottDomainDecodeBHist (scottDomainEncodeBHist A))
            (scottDomainDecodeBHist (scottDomainEncodeBHist V))
            (scottDomainDecodeBHist (scottDomainEncodeBHist R))
            (scottDomainDecodeBHist (scottDomainEncodeBHist H))
            (scottDomainDecodeBHist (scottDomainEncodeBHist C))
            (scottDomainDecodeBHist (scottDomainEncodeBHist P))
            (scottDomainDecodeBHist (scottDomainEncodeBHist N))) =
          some (ScottDomainUp.mk O S U B A V R H C P N)
      rw [ScottDomainTasteGate_single_carrier_alignment_decode_encode O,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode S,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode U,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode B,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode A,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode V,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode R,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode H,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode C,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode P,
        ScottDomainTasteGate_single_carrier_alignment_decode_encode N]

private theorem ScottDomainTasteGate_single_carrier_alignment_ToEventFlow_injective
    {x y : ScottDomainUp} :
    scottDomainToEventFlow x = scottDomainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = scottDomainFromEventFlow (scottDomainToEventFlow x) :=
        (ScottDomainTasteGate_single_carrier_alignment_round_trip x).symm
      _ = scottDomainFromEventFlow (scottDomainToEventFlow y) :=
        congrArg scottDomainFromEventFlow hxy
      _ = some y :=
        ScottDomainTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance ScottDomainTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ScottDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := scottDomainToEventFlow
  fromEventFlow := scottDomainFromEventFlow

instance ScottDomainTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ScottDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change scottDomainFromEventFlow (scottDomainToEventFlow x) = some x
    exact ScottDomainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ScottDomainTasteGate_single_carrier_alignment_ToEventFlow_injective heq)

theorem ScottDomainTasteGate_single_carrier_alignment :
    (∀ h : BHist, scottDomainDecodeBHist (scottDomainEncodeBHist h) = h) ∧
      scottDomainFields
          (ScottDomainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        scottDomainEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ScottDomainTasteGate_single_carrier_alignment_decode_encode,
      rfl,
      rfl⟩

end BEDC.Derived.ScottDomainUp
