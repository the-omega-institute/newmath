import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CUNSpectralAntennaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CUNSpectralAntennaUp : Type where
  | mk (T R P E M S H C Q N : BHist) : CUNSpectralAntennaUp
  deriving DecidableEq

def cunSpectralAntennaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cunSpectralAntennaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cunSpectralAntennaEncodeBHist h

def cunSpectralAntennaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cunSpectralAntennaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cunSpectralAntennaDecodeBHist tail)

private theorem CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cunSpectralAntennaFields : CUNSpectralAntennaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CUNSpectralAntennaUp.mk T R P E M S H C Q N => [T, R, P, E, M, S, H, C, Q, N]

def cunSpectralAntennaToEventFlow : CUNSpectralAntennaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cunSpectralAntennaFields x).map cunSpectralAntennaEncodeBHist

private def cunSpectralAntennaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cunSpectralAntennaEventAtDefault index rest

def cunSpectralAntennaFromEventFlow
    (ef : EventFlow) : Option CUNSpectralAntennaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CUNSpectralAntennaUp.mk
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 0 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 1 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 2 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 3 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 4 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 5 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 6 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 7 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 8 ef))
      (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEventAtDefault 9 ef)))

private theorem CUNSpectralAntennaTasteGate_single_carrier_alignment_round_trip
    (x : CUNSpectralAntennaUp) :
    cunSpectralAntennaFromEventFlow (cunSpectralAntennaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T R P E M S H C Q N =>
      change
        some
          (CUNSpectralAntennaUp.mk
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist T))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist R))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist P))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist E))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist M))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist S))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist H))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist C))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist Q))
            (cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist N))) =
          some (CUNSpectralAntennaUp.mk T R P E M S H C Q N)
      rw [CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode T,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode R,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode P,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode E,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode M,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode S,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode H,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode C,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode Q,
        CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode N]

private theorem CUNSpectralAntennaTasteGate_single_carrier_alignment_injective
    {x y : CUNSpectralAntennaUp} :
    cunSpectralAntennaToEventFlow x = cunSpectralAntennaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cunSpectralAntennaFromEventFlow (cunSpectralAntennaToEventFlow x) =
        cunSpectralAntennaFromEventFlow (cunSpectralAntennaToEventFlow y) :=
    congrArg cunSpectralAntennaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CUNSpectralAntennaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CUNSpectralAntennaTasteGate_single_carrier_alignment_round_trip y)))

private theorem CUNSpectralAntennaTasteGate_single_carrier_alignment_fields :
    ∀ x y : CUNSpectralAntennaUp,
      cunSpectralAntennaFields x = cunSpectralAntennaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ R₁ P₁ E₁ M₁ S₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk T₂ R₂ P₂ E₂ M₂ S₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance cunSpectralAntennaBHistCarrier : BHistCarrier CUNSpectralAntennaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cunSpectralAntennaToEventFlow
  fromEventFlow := cunSpectralAntennaFromEventFlow

instance cunSpectralAntennaChapterTasteGate : ChapterTasteGate CUNSpectralAntennaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cunSpectralAntennaFromEventFlow (cunSpectralAntennaToEventFlow x) = some x
    exact CUNSpectralAntennaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CUNSpectralAntennaTasteGate_single_carrier_alignment_injective heq)

instance cunSpectralAntennaFieldFaithful : FieldFaithful CUNSpectralAntennaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cunSpectralAntennaFields
  field_faithful := CUNSpectralAntennaTasteGate_single_carrier_alignment_fields

instance cunSpectralAntennaNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CUNSpectralAntennaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CUNSpectralAntennaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CUNSpectralAntennaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CUNSpectralAntennaTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CUNSpectralAntennaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cunSpectralAntennaChapterTasteGate

theorem CUNSpectralAntennaTasteGate_single_carrier_alignment :
    (∀ h : BHist, cunSpectralAntennaDecodeBHist (cunSpectralAntennaEncodeBHist h) = h) ∧
      (∀ x : CUNSpectralAntennaUp,
        cunSpectralAntennaFromEventFlow (cunSpectralAntennaToEventFlow x) = some x) ∧
        (∀ x y : CUNSpectralAntennaUp,
          cunSpectralAntennaToEventFlow x = cunSpectralAntennaToEventFlow y → x = y) ∧
          cunSpectralAntennaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CUNSpectralAntennaTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CUNSpectralAntennaTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CUNSpectralAntennaTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CUNSpectralAntennaUp
