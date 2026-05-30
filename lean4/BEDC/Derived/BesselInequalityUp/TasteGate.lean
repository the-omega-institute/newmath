import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BesselInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BesselInequalityUp : Type where
  | mk (H I N V O C S L T R P Q : BHist) : BesselInequalityUp
  deriving DecidableEq

def besselInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: besselInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: besselInequalityEncodeBHist h

def besselInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (besselInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (besselInequalityDecodeBHist tail)

private theorem BesselInequalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, besselInequalityDecodeBHist (besselInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def besselInequalityFields : BesselInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BesselInequalityUp.mk H I N V O C S L T R P Q => [H, I, N, V, O, C, S, L, T, R, P, Q]

def besselInequalityToEventFlow : BesselInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (besselInequalityFields x).map besselInequalityEncodeBHist

private def besselInequalityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => besselInequalityEventAt index rest

def besselInequalityFromEventFlow (ef : EventFlow) : Option BesselInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BesselInequalityUp.mk
      (besselInequalityDecodeBHist (besselInequalityEventAt 0 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 1 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 2 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 3 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 4 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 5 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 6 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 7 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 8 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 9 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 10 ef))
      (besselInequalityDecodeBHist (besselInequalityEventAt 11 ef)))

private theorem BesselInequalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BesselInequalityUp,
      besselInequalityFromEventFlow (besselInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H I N V O C S L T R P Q =>
      change
        some
          (BesselInequalityUp.mk
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist H))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist I))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist N))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist V))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist O))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist C))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist S))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist L))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist T))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist R))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist P))
            (besselInequalityDecodeBHist (besselInequalityEncodeBHist Q))) =
          some (BesselInequalityUp.mk H I N V O C S L T R P Q)
      rw [BesselInequalityTasteGate_single_carrier_alignment_decode_encode H,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode I,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode N,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode V,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode O,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode C,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode S,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode L,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode T,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode R,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode P,
        BesselInequalityTasteGate_single_carrier_alignment_decode_encode Q]

private theorem BesselInequalityToEventFlow_injective {x y : BesselInequalityUp} :
    besselInequalityToEventFlow x = besselInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      besselInequalityFromEventFlow (besselInequalityToEventFlow x) =
        besselInequalityFromEventFlow (besselInequalityToEventFlow y) :=
    congrArg besselInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BesselInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BesselInequalityTasteGate_single_carrier_alignment_round_trip y)))

private theorem BesselInequalityTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BesselInequalityUp, besselInequalityFields x = besselInequalityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H1 I1 N1 V1 O1 C1 S1 L1 T1 R1 P1 Q1 =>
      cases y with
      | mk H2 I2 N2 V2 O2 C2 S2 L2 T2 R2 P2 Q2 =>
          cases hfields
          rfl

instance besselInequalityBHistCarrier : BHistCarrier BesselInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := besselInequalityToEventFlow
  fromEventFlow := besselInequalityFromEventFlow

instance besselInequalityChapterTasteGate : ChapterTasteGate BesselInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change besselInequalityFromEventFlow (besselInequalityToEventFlow x) = some x
    exact BesselInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BesselInequalityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BesselInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  besselInequalityChapterTasteGate

instance besselInequalityFieldFaithful : FieldFaithful BesselInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := besselInequalityFields
  field_faithful := BesselInequalityTasteGate_single_carrier_alignment_fields_faithful

instance besselInequalityNontrivial : Nontrivial BesselInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BesselInequalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BesselInequalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem BesselInequalityTasteGate_single_carrier_alignment :
    (∀ h : BHist, besselInequalityDecodeBHist (besselInequalityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BesselInequalityUp) ∧
        Nonempty (ChapterTasteGate BesselInequalityUp) ∧
          besselInequalityFields
              (BesselInequalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BesselInequalityTasteGate_single_carrier_alignment_decode_encode,
      ⟨besselInequalityBHistCarrier⟩,
      ⟨besselInequalityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BesselInequalityUp
