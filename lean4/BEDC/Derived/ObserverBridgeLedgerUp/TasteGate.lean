import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverBridgeLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverBridgeLedgerUp : Type where
  | mk (S Q M I L R H C P N : BHist) : ObserverBridgeLedgerUp
  deriving DecidableEq

def observerBridgeLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerBridgeLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerBridgeLedgerEncodeBHist h

def observerBridgeLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerBridgeLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerBridgeLedgerDecodeBHist tail)

private theorem ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      observerBridgeLedgerDecodeBHist
        (observerBridgeLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerBridgeLedgerFields :
    ObserverBridgeLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverBridgeLedgerUp.mk S Q M I L R H C P N => [S, Q, M, I, L, R, H, C, P, N]

def observerBridgeLedgerToEventFlow :
    ObserverBridgeLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (observerBridgeLedgerFields x).map observerBridgeLedgerEncodeBHist

def observerBridgeLedgerFromEventFlow :
    EventFlow → Option ObserverBridgeLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
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
                                                (ObserverBridgeLedgerUp.mk
                                                  (observerBridgeLedgerDecodeBHist S)
                                                  (observerBridgeLedgerDecodeBHist Q)
                                                  (observerBridgeLedgerDecodeBHist M)
                                                  (observerBridgeLedgerDecodeBHist I)
                                                  (observerBridgeLedgerDecodeBHist L)
                                                  (observerBridgeLedgerDecodeBHist R)
                                                  (observerBridgeLedgerDecodeBHist H)
                                                  (observerBridgeLedgerDecodeBHist C)
                                                  (observerBridgeLedgerDecodeBHist P)
                                                  (observerBridgeLedgerDecodeBHist N))
                                          | _ :: _ => none

private theorem ObserverBridgeLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ObserverBridgeLedgerUp,
      observerBridgeLedgerFromEventFlow
        (observerBridgeLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q M I L R H C P N =>
      change
        some
          (ObserverBridgeLedgerUp.mk
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist S))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist Q))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist M))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist I))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist L))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist R))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist H))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist C))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist P))
            (observerBridgeLedgerDecodeBHist (observerBridgeLedgerEncodeBHist N))) =
          some (ObserverBridgeLedgerUp.mk S Q M I L R H C P N)
      rw [ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode S,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode Q,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode M,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode I,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode L,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode R,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode H,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode C,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode P,
        ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode N]

private theorem ObserverBridgeLedgerTasteGate_single_carrier_alignment_injective
    {x y : ObserverBridgeLedgerUp} :
    observerBridgeLedgerToEventFlow x =
      observerBridgeLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerBridgeLedgerFromEventFlow
          (observerBridgeLedgerToEventFlow x) =
        observerBridgeLedgerFromEventFlow
          (observerBridgeLedgerToEventFlow y) :=
    congrArg observerBridgeLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ObserverBridgeLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ObserverBridgeLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem observerBridgeLedger_field_faithful :
    ∀ x y : ObserverBridgeLedgerUp,
      observerBridgeLedgerFields x = observerBridgeLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Q₁ M₁ I₁ L₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ M₂ I₂ L₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance observerBridgeLedgerBHistCarrier :
    BHistCarrier ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerBridgeLedgerToEventFlow
  fromEventFlow := observerBridgeLedgerFromEventFlow

instance observerBridgeLedgerChapterTasteGate :
    ChapterTasteGate ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerBridgeLedgerFromEventFlow
        (observerBridgeLedgerToEventFlow x) = some x
    exact ObserverBridgeLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ObserverBridgeLedgerTasteGate_single_carrier_alignment_injective heq)

instance observerBridgeLedgerFieldFaithful :
    FieldFaithful ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerBridgeLedgerFields
  field_faithful := observerBridgeLedger_field_faithful

instance observerBridgeLedgerNontrivial :
    Nontrivial ObserverBridgeLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverBridgeLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverBridgeLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverBridgeLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerBridgeLedgerChapterTasteGate

theorem ObserverBridgeLedgerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ObserverBridgeLedgerUp) ∧
      Nonempty (FieldFaithful ObserverBridgeLedgerUp) ∧
        Nonempty (Nontrivial ObserverBridgeLedgerUp) ∧
          (∀ h : BHist,
            observerBridgeLedgerDecodeBHist
              (observerBridgeLedgerEncodeBHist h) = h) ∧
            (∀ x : ObserverBridgeLedgerUp,
              observerBridgeLedgerFromEventFlow
                (observerBridgeLedgerToEventFlow x) = some x) ∧
              (∀ x y : ObserverBridgeLedgerUp,
                observerBridgeLedgerToEventFlow x =
                    observerBridgeLedgerToEventFlow y →
                  x = y) ∧
                observerBridgeLedgerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨observerBridgeLedgerChapterTasteGate⟩,
      ⟨observerBridgeLedgerFieldFaithful⟩,
      ⟨observerBridgeLedgerNontrivial⟩,
      ObserverBridgeLedgerTasteGate_single_carrier_alignment_decode_encode,
      ObserverBridgeLedgerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ObserverBridgeLedgerTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.ObserverBridgeLedgerUp.TasteGate
