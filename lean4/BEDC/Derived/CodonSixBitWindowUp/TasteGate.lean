import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CodonSixBitWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CodonSixBitWindowUp : Type where
  | mk (B A L F S H C P N : BHist) : CodonSixBitWindowUp
  deriving DecidableEq

def codonSixBitWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: codonSixBitWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: codonSixBitWindowEncodeBHist h

def codonSixBitWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (codonSixBitWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (codonSixBitWindowDecodeBHist tail)

private theorem CodonSixBitWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def codonSixBitWindowFields : CodonSixBitWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CodonSixBitWindowUp.mk B A L F S H C P N => [B, A, L, F, S, H, C, P, N]

def codonSixBitWindowToEventFlow : CodonSixBitWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (codonSixBitWindowFields x).map codonSixBitWindowEncodeBHist

def codonSixBitWindowEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => codonSixBitWindowEventAt index rest

def codonSixBitWindowFromEventFlow : EventFlow → Option CodonSixBitWindowUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (CodonSixBitWindowUp.mk
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 0 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 1 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 2 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 3 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 4 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 5 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 6 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 7 flow))
          (codonSixBitWindowDecodeBHist (codonSixBitWindowEventAt 8 flow)))

private theorem CodonSixBitWindowTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CodonSixBitWindowUp,
      codonSixBitWindowFromEventFlow (codonSixBitWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A L F S H C P N =>
      change
        some
          (CodonSixBitWindowUp.mk
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist B))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist A))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist L))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist F))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist S))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist H))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist C))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist P))
            (codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist N))) =
          some (CodonSixBitWindowUp.mk B A L F S H C P N)
      rw [CodonSixBitWindowTasteGate_single_carrier_alignment_decode B,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode A,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode L,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode F,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode S,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode H,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode C,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode P,
        CodonSixBitWindowTasteGate_single_carrier_alignment_decode N]

private theorem codonSixBitWindowToEventFlow_injective {x y : CodonSixBitWindowUp} :
    codonSixBitWindowToEventFlow x = codonSixBitWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      codonSixBitWindowFromEventFlow (codonSixBitWindowToEventFlow x) =
        codonSixBitWindowFromEventFlow (codonSixBitWindowToEventFlow y) :=
    congrArg codonSixBitWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CodonSixBitWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CodonSixBitWindowTasteGate_single_carrier_alignment_round_trip y)))

private theorem CodonSixBitWindowTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CodonSixBitWindowUp, codonSixBitWindowFields x = codonSixBitWindowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 A1 L1 F1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 A2 L2 F2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance codonSixBitWindowBHistCarrier : BHistCarrier CodonSixBitWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := codonSixBitWindowToEventFlow
  fromEventFlow := codonSixBitWindowFromEventFlow

instance codonSixBitWindowChapterTasteGate : ChapterTasteGate CodonSixBitWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change codonSixBitWindowFromEventFlow (codonSixBitWindowToEventFlow x) = some x
    exact CodonSixBitWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (codonSixBitWindowToEventFlow_injective heq)

instance codonSixBitWindowFieldFaithful : FieldFaithful CodonSixBitWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := codonSixBitWindowFields
  field_faithful := CodonSixBitWindowTasteGate_single_carrier_alignment_fields_faithful

instance codonSixBitWindowNontrivial : Nontrivial CodonSixBitWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CodonSixBitWindowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CodonSixBitWindowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CodonSixBitWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  codonSixBitWindowChapterTasteGate

theorem CodonSixBitWindowTasteGate_single_carrier_alignment :
    (forall h : BHist, codonSixBitWindowDecodeBHist (codonSixBitWindowEncodeBHist h) = h) ∧
      codonSixBitWindowFields
          (CodonSixBitWindowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact ⟨CodonSixBitWindowTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.CodonSixBitWindowUp
