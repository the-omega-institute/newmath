import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplyFailureWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplyFailureWitnessUp : Type where
  | mk (B R F D T G H C P N : BHist) : ExternalSupplyFailureWitnessUp
  deriving DecidableEq

def externalSupplyFailureWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplyFailureWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplyFailureWitnessEncodeBHist h

def externalSupplyFailureWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplyFailureWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplyFailureWitnessDecodeBHist tail)

private theorem externalSupplyFailureWitness_decode_encode_bhist :
    ∀ h : BHist,
      externalSupplyFailureWitnessDecodeBHist
        (externalSupplyFailureWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem externalSupplyFailureWitness_mk_congr
    {B B' R R' F F' D D' T T' G G' H H' C C' P P' N N' : BHist}
    (hB : B' = B) (hR : R' = R) (hF : F' = F) (hD : D' = D) (hT : T' = T)
    (hG : G' = G) (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ExternalSupplyFailureWitnessUp.mk B' R' F' D' T' G' H' C' P' N' =
      ExternalSupplyFailureWitnessUp.mk B R F D T G H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hR
  cases hF
  cases hD
  cases hT
  cases hG
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private def externalSupplyFailureWitnessFields :
    ExternalSupplyFailureWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplyFailureWitnessUp.mk B R F D T G H C P N => [B, R, F, D, T, G, H, C, P, N]

def externalSupplyFailureWitnessToEventFlow :
    ExternalSupplyFailureWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (externalSupplyFailureWitnessFields x).map externalSupplyFailureWitnessEncodeBHist

private def externalSupplyFailureWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => externalSupplyFailureWitnessEventAtDefault index rest

def externalSupplyFailureWitnessFromEventFlow :
    EventFlow → Option ExternalSupplyFailureWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ExternalSupplyFailureWitnessUp.mk
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 0 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 1 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 2 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 3 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 4 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 5 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 6 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 7 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 8 ef))
        (externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEventAtDefault 9 ef)))

private theorem externalSupplyFailureWitness_round_trip :
    ∀ x : ExternalSupplyFailureWitnessUp,
      externalSupplyFailureWitnessFromEventFlow
        (externalSupplyFailureWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B R F D T G H C P N =>
      exact
        congrArg some
          (externalSupplyFailureWitness_mk_congr
            (externalSupplyFailureWitness_decode_encode_bhist B)
            (externalSupplyFailureWitness_decode_encode_bhist R)
            (externalSupplyFailureWitness_decode_encode_bhist F)
            (externalSupplyFailureWitness_decode_encode_bhist D)
            (externalSupplyFailureWitness_decode_encode_bhist T)
            (externalSupplyFailureWitness_decode_encode_bhist G)
            (externalSupplyFailureWitness_decode_encode_bhist H)
            (externalSupplyFailureWitness_decode_encode_bhist C)
            (externalSupplyFailureWitness_decode_encode_bhist P)
            (externalSupplyFailureWitness_decode_encode_bhist N))

private theorem externalSupplyFailureWitnessToEventFlow_injective
    {x y : ExternalSupplyFailureWitnessUp} :
    externalSupplyFailureWitnessToEventFlow x = externalSupplyFailureWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplyFailureWitnessFromEventFlow
          (externalSupplyFailureWitnessToEventFlow x) =
        externalSupplyFailureWitnessFromEventFlow
          (externalSupplyFailureWitnessToEventFlow y) :=
    congrArg externalSupplyFailureWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalSupplyFailureWitness_round_trip x).symm
      (Eq.trans hread (externalSupplyFailureWitness_round_trip y)))

private theorem externalSupplyFailureWitness_field_faithful :
    ∀ x y : ExternalSupplyFailureWitnessUp,
      externalSupplyFailureWitnessFields x = externalSupplyFailureWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B R F D T G H C P N =>
      cases y with
      | mk B' R' F' D' T' G' H' C' P' N' =>
          cases hfields
          rfl

instance externalSupplyFailureWitnessBHistCarrier :
    BHistCarrier ExternalSupplyFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplyFailureWitnessToEventFlow
  fromEventFlow := externalSupplyFailureWitnessFromEventFlow

instance externalSupplyFailureWitnessChapterTasteGate :
    ChapterTasteGate ExternalSupplyFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      externalSupplyFailureWitnessFromEventFlow
        (externalSupplyFailureWitnessToEventFlow x) = some x
    exact externalSupplyFailureWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplyFailureWitnessToEventFlow_injective heq)

instance externalSupplyFailureWitnessFieldFaithful :
    FieldFaithful ExternalSupplyFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := externalSupplyFailureWitnessFields
  field_faithful := externalSupplyFailureWitness_field_faithful

instance externalSupplyFailureWitnessNontrivial :
    Nontrivial ExternalSupplyFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplyFailureWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplyFailureWitnessUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ExternalSupplyFailureWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  externalSupplyFailureWitnessChapterTasteGate

theorem ExternalSupplyFailureWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      externalSupplyFailureWitnessDecodeBHist
        (externalSupplyFailureWitnessEncodeBHist h) = h) ∧
      (∀ x : ExternalSupplyFailureWitnessUp,
        externalSupplyFailureWitnessFromEventFlow
          (externalSupplyFailureWitnessToEventFlow x) = some x) ∧
        (∀ x y : ExternalSupplyFailureWitnessUp,
          externalSupplyFailureWitnessToEventFlow x =
              externalSupplyFailureWitnessToEventFlow y →
            x = y) ∧
          Nonempty (ChapterTasteGate ExternalSupplyFailureWitnessUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨externalSupplyFailureWitness_decode_encode_bhist,
      externalSupplyFailureWitness_round_trip,
      (fun _ _ heq => externalSupplyFailureWitnessToEventFlow_injective heq),
      ⟨externalSupplyFailureWitnessChapterTasteGate⟩⟩

end BEDC.Derived.ExternalSupplyFailureWitnessUp
