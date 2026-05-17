import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EpistemicOntologyBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EpistemicOntologyBridgeUp : Type where
  | mk : (O K Q P A L H C R N : BHist) → EpistemicOntologyBridgeUp
  deriving DecidableEq

def epistemicOntologyBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: epistemicOntologyBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: epistemicOntologyBridgeEncodeBHist h

def epistemicOntologyBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (epistemicOntologyBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (epistemicOntologyBridgeDecodeBHist tail)

private theorem epistemicOntologyBridgeDecode_encode_bhist :
    ∀ h : BHist,
      epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def epistemicOntologyBridgeToEventFlow : EpistemicOntologyBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EpistemicOntologyBridgeUp.mk O K Q P A L H C R N =>
      [[BMark.b0],
        epistemicOntologyBridgeEncodeBHist O,
        [BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        epistemicOntologyBridgeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        epistemicOntologyBridgeEncodeBHist N]

private def epistemicOntologyBridgeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => epistemicOntologyBridgeRawAt n rest

private def epistemicOntologyBridgeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => epistemicOntologyBridgeLengthEq n rest

def epistemicOntologyBridgeFromEventFlow : EventFlow → Option EpistemicOntologyBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match epistemicOntologyBridgeLengthEq 20 flow with
      | true =>
          some
            (EpistemicOntologyBridgeUp.mk
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 1 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 3 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 5 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 7 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 9 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 11 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 13 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 15 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 17 flow))
              (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeRawAt 19 flow)))
      | false => none

private theorem epistemicOntologyBridge_round_trip :
    ∀ x : EpistemicOntologyBridgeUp,
      epistemicOntologyBridgeFromEventFlow (epistemicOntologyBridgeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O K Q P A L H C R N =>
      change
        some
          (EpistemicOntologyBridgeUp.mk
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist O))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist K))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist Q))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist P))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist A))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist L))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist H))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist C))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist R))
            (epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist N))) =
          some (EpistemicOntologyBridgeUp.mk O K Q P A L H C R N)
      rw [epistemicOntologyBridgeDecode_encode_bhist O,
        epistemicOntologyBridgeDecode_encode_bhist K,
        epistemicOntologyBridgeDecode_encode_bhist Q,
        epistemicOntologyBridgeDecode_encode_bhist P,
        epistemicOntologyBridgeDecode_encode_bhist A,
        epistemicOntologyBridgeDecode_encode_bhist L,
        epistemicOntologyBridgeDecode_encode_bhist H,
        epistemicOntologyBridgeDecode_encode_bhist C,
        epistemicOntologyBridgeDecode_encode_bhist R,
        epistemicOntologyBridgeDecode_encode_bhist N]

private theorem epistemicOntologyBridgeToEventFlow_injective
    {x y : EpistemicOntologyBridgeUp} :
    epistemicOntologyBridgeToEventFlow x = epistemicOntologyBridgeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      epistemicOntologyBridgeFromEventFlow (epistemicOntologyBridgeToEventFlow x) =
        epistemicOntologyBridgeFromEventFlow (epistemicOntologyBridgeToEventFlow y) :=
    congrArg epistemicOntologyBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (epistemicOntologyBridge_round_trip x).symm
      (Eq.trans hread (epistemicOntologyBridge_round_trip y)))

instance epistemicOntologyBridgeBHistCarrier :
    BHistCarrier EpistemicOntologyBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := epistemicOntologyBridgeToEventFlow
  fromEventFlow := epistemicOntologyBridgeFromEventFlow

instance epistemicOntologyBridgeChapterTasteGate :
    ChapterTasteGate EpistemicOntologyBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      epistemicOntologyBridgeFromEventFlow (epistemicOntologyBridgeToEventFlow x) =
        some x
    exact epistemicOntologyBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (epistemicOntologyBridgeToEventFlow_injective heq)

instance epistemicOntologyBridgeFieldFaithful :
    FieldFaithful EpistemicOntologyBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | EpistemicOntologyBridgeUp.mk O K Q P A L H C R N => [O, K, Q, P, A, L, H, C, R, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk O1 K1 Q1 P1 A1 L1 H1 C1 R1 N1 =>
        cases y with
        | mk O2 K2 Q2 P2 A2 L2 H2 C2 R2 N2 =>
            cases h
            rfl

instance epistemicOntologyBridgeNontrivial :
    Nontrivial EpistemicOntologyBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EpistemicOntologyBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EpistemicOntologyBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EpistemicOntologyBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  epistemicOntologyBridgeChapterTasteGate

theorem EpistemicOntologyBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      epistemicOntologyBridgeDecodeBHist (epistemicOntologyBridgeEncodeBHist h) = h) ∧
      (∀ x : EpistemicOntologyBridgeUp,
        epistemicOntologyBridgeFromEventFlow (epistemicOntologyBridgeToEventFlow x) =
          some x) ∧
      (∀ x y : EpistemicOntologyBridgeUp,
        epistemicOntologyBridgeToEventFlow x = epistemicOntologyBridgeToEventFlow y →
          x = y) ∧
      (∃ x y : EpistemicOntologyBridgeUp, x ≠ y) ∧
      epistemicOntologyBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact epistemicOntologyBridgeDecode_encode_bhist
  · constructor
    · exact epistemicOntologyBridge_round_trip
    · constructor
      · intro x y heq
        exact epistemicOntologyBridgeToEventFlow_injective heq
      · constructor
        · exact
            ⟨EpistemicOntologyBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              EpistemicOntologyBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty,
              by
                intro h
                cases h⟩
        · rfl

end BEDC.Derived.EpistemicOntologyBridgeUp
