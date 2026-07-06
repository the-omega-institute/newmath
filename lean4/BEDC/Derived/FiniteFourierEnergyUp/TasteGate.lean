import BEDC.Derived.FiniteFourierEnergyUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteFourierEnergyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteFourierEnergyUp : Type where
  | mk :
      (fourier parseval circle pairing integral rational dyadic realSeal transport replay
        provenance name : BHist) →
        FiniteFourierEnergyUp
  deriving DecidableEq

def finiteFourierEnergyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteFourierEnergyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteFourierEnergyEncodeBHist h

def finiteFourierEnergyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteFourierEnergyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteFourierEnergyDecodeBHist tail)

private theorem finiteFourierEnergy_decode_encode_bhist :
    ∀ h : BHist, finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteFourierEnergyFields : FiniteFourierEnergyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteFourierEnergyUp.mk fourier parseval circle pairing integral rational dyadic realSeal
      transport replay provenance name =>
      [fourier, parseval, circle, pairing, integral, rational, dyadic, realSeal, transport,
        replay, provenance, name]

def finiteFourierEnergyToEventFlow : FiniteFourierEnergyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map finiteFourierEnergyEncodeBHist (finiteFourierEnergyFields x)

private def finiteFourierEnergyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteFourierEnergyEventAtDefault index rest

def finiteFourierEnergyFromEventFlow (ef : EventFlow) : Option FiniteFourierEnergyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteFourierEnergyUp.mk
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 0 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 1 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 2 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 3 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 4 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 5 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 6 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 7 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 8 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 9 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 10 ef))
      (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEventAtDefault 11 ef)))

private theorem finiteFourierEnergy_round_trip :
    ∀ x : FiniteFourierEnergyUp,
      finiteFourierEnergyFromEventFlow (finiteFourierEnergyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fourier parseval circle pairing integral rational dyadic realSeal transport replay
      provenance name =>
      change
        some
          (FiniteFourierEnergyUp.mk
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist fourier))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist parseval))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist circle))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist pairing))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist integral))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist rational))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist dyadic))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist realSeal))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist transport))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist replay))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist provenance))
            (finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist name))) =
          some
            (FiniteFourierEnergyUp.mk fourier parseval circle pairing integral rational dyadic
              realSeal transport replay provenance name)
      rw [finiteFourierEnergy_decode_encode_bhist fourier,
        finiteFourierEnergy_decode_encode_bhist parseval,
        finiteFourierEnergy_decode_encode_bhist circle,
        finiteFourierEnergy_decode_encode_bhist pairing,
        finiteFourierEnergy_decode_encode_bhist integral,
        finiteFourierEnergy_decode_encode_bhist rational,
        finiteFourierEnergy_decode_encode_bhist dyadic,
        finiteFourierEnergy_decode_encode_bhist realSeal,
        finiteFourierEnergy_decode_encode_bhist transport,
        finiteFourierEnergy_decode_encode_bhist replay,
        finiteFourierEnergy_decode_encode_bhist provenance,
        finiteFourierEnergy_decode_encode_bhist name]

private theorem finiteFourierEnergyToEventFlow_injective {x y : FiniteFourierEnergyUp} :
    finiteFourierEnergyToEventFlow x = finiteFourierEnergyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteFourierEnergyFromEventFlow (finiteFourierEnergyToEventFlow x) =
        finiteFourierEnergyFromEventFlow (finiteFourierEnergyToEventFlow y) :=
    congrArg finiteFourierEnergyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteFourierEnergy_round_trip x).symm
      (Eq.trans hread (finiteFourierEnergy_round_trip y)))

private theorem finiteFourierEnergy_field_faithful :
    ∀ x y : FiniteFourierEnergyUp, finiteFourierEnergyFields x = finiteFourierEnergyFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk fourier₁ parseval₁ circle₁ pairing₁ integral₁ rational₁ dyadic₁ realSeal₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk fourier₂ parseval₂ circle₂ pairing₂ integral₂ rational₂ dyadic₂ realSeal₂
          transport₂ replay₂ provenance₂ name₂ =>
          cases h
          rfl

instance finiteFourierEnergyBHistCarrier : BHistCarrier FiniteFourierEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteFourierEnergyToEventFlow
  fromEventFlow := finiteFourierEnergyFromEventFlow

instance finiteFourierEnergyChapterTasteGate : ChapterTasteGate FiniteFourierEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteFourierEnergyFromEventFlow (finiteFourierEnergyToEventFlow x) = some x
    exact finiteFourierEnergy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteFourierEnergyToEventFlow_injective heq)

instance finiteFourierEnergyFieldFaithful : FieldFaithful FiniteFourierEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteFourierEnergyFields
  field_faithful := finiteFourierEnergy_field_faithful

instance finiteFourierEnergyNontrivial : Nontrivial FiniteFourierEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteFourierEnergyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteFourierEnergyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteFourierEnergyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteFourierEnergyChapterTasteGate

theorem FiniteFourierEnergyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteFourierEnergyUp) ∧
      Nonempty (FieldFaithful FiniteFourierEnergyUp) ∧
        Nonempty (Nontrivial FiniteFourierEnergyUp) ∧
          (∀ h : BHist, finiteFourierEnergyDecodeBHist (finiteFourierEnergyEncodeBHist h) = h) ∧
            (∀ x : FiniteFourierEnergyUp,
              finiteFourierEnergyFromEventFlow (finiteFourierEnergyToEventFlow x) = some x) ∧
              (∀ x y : FiniteFourierEnergyUp,
                finiteFourierEnergyToEventFlow x = finiteFourierEnergyToEventFlow y →
                  x = y) ∧
                finiteFourierEnergyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨finiteFourierEnergyChapterTasteGate⟩, ⟨finiteFourierEnergyFieldFaithful⟩,
      ⟨finiteFourierEnergyNontrivial⟩, finiteFourierEnergy_decode_encode_bhist,
      finiteFourierEnergy_round_trip,
      (fun _x _y heq => finiteFourierEnergyToEventFlow_injective heq), rfl⟩

end BEDC.Derived.FiniteFourierEnergyUp
