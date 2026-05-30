import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HenstockKurzweilUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HenstockKurzweilUp : Type where
  | mk (G I S W D R E H C P N : BHist) : HenstockKurzweilUp
  deriving DecidableEq

def henstockKurzweilEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: henstockKurzweilEncodeBHist h
  | BHist.e1 h => BMark.b1 :: henstockKurzweilEncodeBHist h

def henstockKurzweilDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (henstockKurzweilDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (henstockKurzweilDecodeBHist tail)

private theorem HenstockKurzweilTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def henstockKurzweilFields : HenstockKurzweilUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HenstockKurzweilUp.mk G I S W D R E H C P N => [G, I, S, W, D, R, E, H, C, P, N]

def henstockKurzweilToEventFlow : HenstockKurzweilUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (henstockKurzweilFields x).map henstockKurzweilEncodeBHist

private def henstockKurzweilEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => henstockKurzweilEventAtDefault index rest

def henstockKurzweilFromEventFlow (ef : EventFlow) : Option HenstockKurzweilUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HenstockKurzweilUp.mk
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 0 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 1 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 2 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 3 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 4 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 5 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 6 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 7 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 8 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 9 ef))
      (henstockKurzweilDecodeBHist (henstockKurzweilEventAtDefault 10 ef)))

private theorem HenstockKurzweilTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HenstockKurzweilUp,
      henstockKurzweilFromEventFlow (henstockKurzweilToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G I S W D R E H C P N =>
      change
        some
          (HenstockKurzweilUp.mk
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist G))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist I))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist S))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist W))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist D))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist R))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist E))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist H))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist C))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist P))
            (henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist N))) =
          some (HenstockKurzweilUp.mk G I S W D R E H C P N)
      rw [HenstockKurzweilTasteGate_single_carrier_alignment_decode G,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode I,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode S,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode W,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode D,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode R,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode E,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode H,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode C,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode P,
        HenstockKurzweilTasteGate_single_carrier_alignment_decode N]

private theorem HenstockKurzweilTasteGate_single_carrier_alignment_injective
    {x y : HenstockKurzweilUp} :
    henstockKurzweilToEventFlow x = henstockKurzweilToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      henstockKurzweilFromEventFlow (henstockKurzweilToEventFlow x) =
        henstockKurzweilFromEventFlow (henstockKurzweilToEventFlow y) :=
    congrArg henstockKurzweilFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HenstockKurzweilTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HenstockKurzweilTasteGate_single_carrier_alignment_round_trip y)))

private theorem HenstockKurzweilTasteGate_single_carrier_alignment_fields :
    ∀ x y : HenstockKurzweilUp, henstockKurzweilFields x = henstockKurzweilFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 I1 S1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk G2 I2 S2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance henstockKurzweilBHistCarrier : BHistCarrier HenstockKurzweilUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := henstockKurzweilToEventFlow
  fromEventFlow := henstockKurzweilFromEventFlow

instance henstockKurzweilChapterTasteGate : ChapterTasteGate HenstockKurzweilUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change henstockKurzweilFromEventFlow (henstockKurzweilToEventFlow x) = some x
    exact HenstockKurzweilTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HenstockKurzweilTasteGate_single_carrier_alignment_injective heq)

instance henstockKurzweilFieldFaithful : FieldFaithful HenstockKurzweilUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := henstockKurzweilFields
  field_faithful := HenstockKurzweilTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate HenstockKurzweilUp :=
  -- BEDC touchpoint anchor: BHist BMark
  henstockKurzweilChapterTasteGate

def taste_gate_witness : FieldFaithful HenstockKurzweilUp :=
  -- BEDC touchpoint anchor: BHist BMark
  henstockKurzweilFieldFaithful

theorem HenstockKurzweilTasteGate_single_carrier_alignment :
    (∀ h : BHist, henstockKurzweilDecodeBHist (henstockKurzweilEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HenstockKurzweilUp) ∧
        Nonempty (ChapterTasteGate HenstockKurzweilUp) ∧
          henstockKurzweilEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · exact ⟨henstockKurzweilBHistCarrier⟩
  constructor
  · exact ⟨henstockKurzweilChapterTasteGate⟩
  · rfl

end BEDC.Derived.HenstockKurzweilUp
