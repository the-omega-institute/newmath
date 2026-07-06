import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BesicovitchCoveringUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BesicovitchCoveringUp : Type where
  | mk (X M R Q S O V F D H C P N : BHist) : BesicovitchCoveringUp
  deriving DecidableEq

def besicovitchCoveringEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: besicovitchCoveringEncodeBHist h
  | BHist.e1 h => BMark.b1 :: besicovitchCoveringEncodeBHist h

def besicovitchCoveringDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (besicovitchCoveringDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (besicovitchCoveringDecodeBHist tail)

private theorem besicovitchCovering_decode_encode_bhist :
    ∀ h : BHist, besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def besicovitchCoveringFields : BesicovitchCoveringUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BesicovitchCoveringUp.mk X M R Q S O V F D H C P N =>
      [X, M, R, Q, S, O, V, F, D, H, C, P, N]

def besicovitchCoveringToEventFlow : BesicovitchCoveringUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (besicovitchCoveringFields x).map besicovitchCoveringEncodeBHist

private def besicovitchCoveringRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => besicovitchCoveringRawAt index rest

def besicovitchCoveringFromEventFlow (flow : EventFlow) : Option BesicovitchCoveringUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BesicovitchCoveringUp.mk
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 0 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 1 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 2 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 3 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 4 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 5 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 6 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 7 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 8 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 9 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 10 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 11 flow))
      (besicovitchCoveringDecodeBHist (besicovitchCoveringRawAt 12 flow)))

private theorem besicovitchCovering_round_trip :
    ∀ x : BesicovitchCoveringUp,
      besicovitchCoveringFromEventFlow (besicovitchCoveringToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M R Q S O V F D H C P N =>
      change
        some
          (BesicovitchCoveringUp.mk
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist X))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist M))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist R))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist Q))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist S))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist O))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist V))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist F))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist D))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist H))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist C))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist P))
            (besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist N))) =
          some (BesicovitchCoveringUp.mk X M R Q S O V F D H C P N)
      rw [besicovitchCovering_decode_encode_bhist X,
        besicovitchCovering_decode_encode_bhist M,
        besicovitchCovering_decode_encode_bhist R,
        besicovitchCovering_decode_encode_bhist Q,
        besicovitchCovering_decode_encode_bhist S,
        besicovitchCovering_decode_encode_bhist O,
        besicovitchCovering_decode_encode_bhist V,
        besicovitchCovering_decode_encode_bhist F,
        besicovitchCovering_decode_encode_bhist D,
        besicovitchCovering_decode_encode_bhist H,
        besicovitchCovering_decode_encode_bhist C,
        besicovitchCovering_decode_encode_bhist P,
        besicovitchCovering_decode_encode_bhist N]

private theorem besicovitchCoveringToEventFlow_injective {x y : BesicovitchCoveringUp} :
    besicovitchCoveringToEventFlow x = besicovitchCoveringToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          besicovitchCoveringFromEventFlow (besicovitchCoveringToEventFlow x) :=
        (besicovitchCovering_round_trip x).symm
      _ = besicovitchCoveringFromEventFlow (besicovitchCoveringToEventFlow y) :=
        congrArg besicovitchCoveringFromEventFlow hxy
      _ = some y := besicovitchCovering_round_trip y
  exact Option.some.inj optionEq

private theorem besicovitchCovering_fields_faithful :
    ∀ x y : BesicovitchCoveringUp,
      besicovitchCoveringFields x = besicovitchCoveringFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 M1 R1 Q1 S1 O1 V1 F1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 M2 R2 Q2 S2 O2 V2 F2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance besicovitchCoveringBHistCarrier : BHistCarrier BesicovitchCoveringUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := besicovitchCoveringToEventFlow
  fromEventFlow := besicovitchCoveringFromEventFlow

instance besicovitchCoveringChapterTasteGate : ChapterTasteGate BesicovitchCoveringUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change besicovitchCoveringFromEventFlow (besicovitchCoveringToEventFlow x) = some x
    exact besicovitchCovering_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (besicovitchCoveringToEventFlow_injective heq)

instance besicovitchCoveringFieldFaithful : FieldFaithful BesicovitchCoveringUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := besicovitchCoveringFields
  field_faithful := besicovitchCovering_fields_faithful

instance besicovitchCoveringNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BesicovitchCoveringUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BesicovitchCoveringUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BesicovitchCoveringUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BesicovitchCoveringTasteGate_single_carrier_alignment :
    (∀ h : BHist, besicovitchCoveringDecodeBHist (besicovitchCoveringEncodeBHist h) = h) ∧
      (∀ x : BesicovitchCoveringUp,
        besicovitchCoveringFromEventFlow (besicovitchCoveringToEventFlow x) = some x) ∧
        (∀ x y : BesicovitchCoveringUp,
          besicovitchCoveringToEventFlow x = besicovitchCoveringToEventFlow y → x = y) ∧
          besicovitchCoveringEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨besicovitchCovering_decode_encode_bhist,
      besicovitchCovering_round_trip,
      (by
        intro x y heq
        exact besicovitchCoveringToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BesicovitchCoveringUp
