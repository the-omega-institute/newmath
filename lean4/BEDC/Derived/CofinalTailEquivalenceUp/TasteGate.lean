import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalTailEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalTailEquivalenceUp : Type where
  | mk (R0 R1 W Q D A H C P N : BHist) : CofinalTailEquivalenceUp
  deriving DecidableEq

def cofinalTailEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalTailEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalTailEquivalenceEncodeBHist h

def cofinalTailEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalTailEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalTailEquivalenceDecodeBHist tail)

private theorem CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cofinalTailEquivalenceDecodeBHist
        (cofinalTailEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cofinalTailEquivalenceFields : CofinalTailEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N => [R0, R1, W, Q, D, A, H, C, P, N]

def cofinalTailEquivalenceToEventFlow : CofinalTailEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N =>
      [cofinalTailEquivalenceEncodeBHist R0,
        cofinalTailEquivalenceEncodeBHist R1,
        cofinalTailEquivalenceEncodeBHist W,
        cofinalTailEquivalenceEncodeBHist Q,
        cofinalTailEquivalenceEncodeBHist D,
        cofinalTailEquivalenceEncodeBHist A,
        cofinalTailEquivalenceEncodeBHist H,
        cofinalTailEquivalenceEncodeBHist C,
        cofinalTailEquivalenceEncodeBHist P,
        cofinalTailEquivalenceEncodeBHist N]

def cofinalTailEquivalenceFromEventFlow : EventFlow → Option CofinalTailEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R0 :: rest0 =>
      match rest0 with
      | [] => none
      | R1 :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CofinalTailEquivalenceUp.mk
                                                  (cofinalTailEquivalenceDecodeBHist R0)
                                                  (cofinalTailEquivalenceDecodeBHist R1)
                                                  (cofinalTailEquivalenceDecodeBHist W)
                                                  (cofinalTailEquivalenceDecodeBHist Q)
                                                  (cofinalTailEquivalenceDecodeBHist D)
                                                  (cofinalTailEquivalenceDecodeBHist A)
                                                  (cofinalTailEquivalenceDecodeBHist H)
                                                  (cofinalTailEquivalenceDecodeBHist C)
                                                  (cofinalTailEquivalenceDecodeBHist P)
                                                  (cofinalTailEquivalenceDecodeBHist N))
                                          | _ :: _ => none

private theorem CofinalTailEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CofinalTailEquivalenceUp,
      cofinalTailEquivalenceFromEventFlow
        (cofinalTailEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 W Q D A H C P N =>
      change
        some
          (CofinalTailEquivalenceUp.mk
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist R0))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist R1))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist W))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist Q))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist D))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist A))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist H))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist C))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist P))
            (cofinalTailEquivalenceDecodeBHist (cofinalTailEquivalenceEncodeBHist N))) =
          some (CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N)
      rw [CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode R0,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode R1,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode W,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode Q,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode D,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode A,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode H,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode C,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode P,
        CofinalTailEquivalenceTasteGate_single_carrier_alignment_decode N]

private theorem CofinalTailEquivalenceTasteGate_single_carrier_alignment_injective
    {x y : CofinalTailEquivalenceUp} :
    cofinalTailEquivalenceToEventFlow x =
      cofinalTailEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalTailEquivalenceFromEventFlow (cofinalTailEquivalenceToEventFlow x) =
        cofinalTailEquivalenceFromEventFlow (cofinalTailEquivalenceToEventFlow y) :=
    congrArg cofinalTailEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CofinalTailEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CofinalTailEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CofinalTailEquivalenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : CofinalTailEquivalenceUp,
      cofinalTailEquivalenceFields x = cofinalTailEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R0₁ R1₁ W₁ Q₁ D₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R0₂ R1₂ W₂ Q₂ D₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cofinalTailEquivalenceBHistCarrier :
    BHistCarrier CofinalTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalTailEquivalenceToEventFlow
  fromEventFlow := cofinalTailEquivalenceFromEventFlow

instance cofinalTailEquivalenceChapterTasteGate :
    ChapterTasteGate CofinalTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalTailEquivalenceFromEventFlow (cofinalTailEquivalenceToEventFlow x) =
      some x
    exact CofinalTailEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CofinalTailEquivalenceTasteGate_single_carrier_alignment_injective heq)

instance cofinalTailEquivalenceFieldFaithful :
    FieldFaithful CofinalTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cofinalTailEquivalenceFields
  field_faithful := CofinalTailEquivalenceTasteGate_single_carrier_alignment_fields

instance cofinalTailEquivalenceNontrivial : Nontrivial CofinalTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalTailEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CofinalTailEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CofinalTailEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalTailEquivalenceChapterTasteGate

theorem CofinalTailEquivalenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CofinalTailEquivalenceUp) ∧
      Nonempty (ChapterTasteGate CofinalTailEquivalenceUp) ∧
        Nonempty (FieldFaithful CofinalTailEquivalenceUp) ∧
          Nonempty (Nontrivial CofinalTailEquivalenceUp) ∧
            cofinalTailEquivalenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨cofinalTailEquivalenceBHistCarrier⟩,
      ⟨cofinalTailEquivalenceChapterTasteGate⟩,
      ⟨cofinalTailEquivalenceFieldFaithful⟩,
      ⟨cofinalTailEquivalenceNontrivial⟩,
      rfl⟩

end BEDC.Derived.CofinalTailEquivalenceUp
