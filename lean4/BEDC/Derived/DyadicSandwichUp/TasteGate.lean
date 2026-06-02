import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicSandwichUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicSandwichUp : Type where
  | mk (L U S D R H C P N : BHist) : DyadicSandwichUp
  deriving DecidableEq

def dyadicSandwichEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicSandwichEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicSandwichEncodeBHist h

def dyadicSandwichDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicSandwichDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicSandwichDecodeBHist tail)

private theorem dyadicSandwichDecodeEncode :
    ∀ h : BHist, dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicSandwichFields : DyadicSandwichUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicSandwichUp.mk L U S D R H C P N => [L, U, S, D, R, H, C, P, N]

def dyadicSandwichToEventFlow : DyadicSandwichUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicSandwichFields x).map dyadicSandwichEncodeBHist

private def dyadicSandwichEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicSandwichEventAt index rest

def dyadicSandwichFromEventFlow (ef : EventFlow) : Option DyadicSandwichUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicSandwichUp.mk
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 0 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 1 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 2 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 3 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 4 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 5 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 6 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 7 ef))
      (dyadicSandwichDecodeBHist (dyadicSandwichEventAt 8 ef)))

private theorem dyadicSandwichRoundTrip (x : DyadicSandwichUp) :
    dyadicSandwichFromEventFlow (dyadicSandwichToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U S D R H C P N =>
      change
        some
          (DyadicSandwichUp.mk
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist L))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist U))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist S))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist D))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist R))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist H))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist C))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist P))
            (dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist N))) =
          some (DyadicSandwichUp.mk L U S D R H C P N)
      rw [dyadicSandwichDecodeEncode L, dyadicSandwichDecodeEncode U,
        dyadicSandwichDecodeEncode S, dyadicSandwichDecodeEncode D,
        dyadicSandwichDecodeEncode R, dyadicSandwichDecodeEncode H,
        dyadicSandwichDecodeEncode C, dyadicSandwichDecodeEncode P,
        dyadicSandwichDecodeEncode N]

private theorem dyadicSandwichToEventFlow_injective {x y : DyadicSandwichUp} :
    dyadicSandwichToEventFlow x = dyadicSandwichToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicSandwichFromEventFlow (dyadicSandwichToEventFlow x) =
        dyadicSandwichFromEventFlow (dyadicSandwichToEventFlow y) :=
    congrArg dyadicSandwichFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicSandwichRoundTrip x).symm
      (Eq.trans hread (dyadicSandwichRoundTrip y)))

private theorem dyadicSandwichFields_faithful :
    ∀ x y : DyadicSandwichUp, dyadicSandwichFields x = dyadicSandwichFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 S1 D1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 S2 D2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicSandwichBHistCarrier : BHistCarrier DyadicSandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicSandwichToEventFlow
  fromEventFlow := dyadicSandwichFromEventFlow

instance dyadicSandwichChapterTasteGate : ChapterTasteGate DyadicSandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicSandwichFromEventFlow (dyadicSandwichToEventFlow x) = some x
    exact dyadicSandwichRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicSandwichToEventFlow_injective heq)

instance dyadicSandwichFieldFaithful : FieldFaithful DyadicSandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicSandwichFields
  field_faithful := dyadicSandwichFields_faithful

instance dyadicSandwichNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicSandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicSandwichUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicSandwichUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicSandwichUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicSandwichChapterTasteGate

def taste_gate_witness : FieldFaithful DyadicSandwichUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicSandwichFieldFaithful

theorem DyadicSandwichTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DyadicSandwichUp) ∧
      Nonempty (ChapterTasteGate DyadicSandwichUp) ∧
        Nonempty (FieldFaithful DyadicSandwichUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicSandwichUp) ∧
            (∀ h : BHist, dyadicSandwichDecodeBHist (dyadicSandwichEncodeBHist h) = h) ∧
              (∀ x : DyadicSandwichUp,
                dyadicSandwichFromEventFlow (dyadicSandwichToEventFlow x) = some x) ∧
                (∀ x y : DyadicSandwichUp,
                  dyadicSandwichToEventFlow x = dyadicSandwichToEventFlow y -> x = y) ∧
                  dyadicSandwichEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨dyadicSandwichBHistCarrier⟩,
      ⟨dyadicSandwichChapterTasteGate⟩,
      ⟨dyadicSandwichFieldFaithful⟩,
      ⟨dyadicSandwichNontrivial⟩,
      dyadicSandwichDecodeEncode,
      dyadicSandwichRoundTrip,
      (fun _ _ heq => dyadicSandwichToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicSandwichUp
