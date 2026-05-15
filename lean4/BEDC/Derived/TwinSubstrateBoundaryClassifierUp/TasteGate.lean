import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TwinSubstrateBoundaryClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TwinSubstrateBoundaryClassifierUp : Type where
  | mk : (M G Q L D H C P N : BHist) -> TwinSubstrateBoundaryClassifierUp
  deriving DecidableEq

def twinSubstrateBoundaryClassifierEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: twinSubstrateBoundaryClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: twinSubstrateBoundaryClassifierEncodeBHist h

def twinSubstrateBoundaryClassifierDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (twinSubstrateBoundaryClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (twinSubstrateBoundaryClassifierDecodeBHist tail)

private theorem twinSubstrateBoundaryClassifierDecode_encode_bhist :
    forall h : BHist,
      twinSubstrateBoundaryClassifierDecodeBHist
        (twinSubstrateBoundaryClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def twinSubstrateBoundaryClassifierFields :
    TwinSubstrateBoundaryClassifierUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N =>
      [M, G, Q, L, D, H, C, P, N]

def twinSubstrateBoundaryClassifierToEventFlow :
    TwinSubstrateBoundaryClassifierUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N =>
      [twinSubstrateBoundaryClassifierEncodeBHist M,
        twinSubstrateBoundaryClassifierEncodeBHist G,
        twinSubstrateBoundaryClassifierEncodeBHist Q,
        twinSubstrateBoundaryClassifierEncodeBHist L,
        twinSubstrateBoundaryClassifierEncodeBHist D,
        twinSubstrateBoundaryClassifierEncodeBHist H,
        twinSubstrateBoundaryClassifierEncodeBHist C,
        twinSubstrateBoundaryClassifierEncodeBHist P,
        twinSubstrateBoundaryClassifierEncodeBHist N]

private def twinSubstrateBoundaryClassifierEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      twinSubstrateBoundaryClassifierEventAtDefault index rest

def twinSubstrateBoundaryClassifierFromEventFlow :
    EventFlow -> Option TwinSubstrateBoundaryClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (TwinSubstrateBoundaryClassifierUp.mk
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 0 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 1 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 2 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 3 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 4 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 5 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 6 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 7 ef))
          (twinSubstrateBoundaryClassifierDecodeBHist
            (twinSubstrateBoundaryClassifierEventAtDefault 8 ef)))

private theorem twinSubstrateBoundaryClassifier_round_trip :
    forall x : TwinSubstrateBoundaryClassifierUp,
      twinSubstrateBoundaryClassifierFromEventFlow
        (twinSubstrateBoundaryClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M G Q L D H C P N =>
      change
        some
            (TwinSubstrateBoundaryClassifierUp.mk
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist M))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist G))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist Q))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist L))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist D))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist H))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist C))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist P))
              (twinSubstrateBoundaryClassifierDecodeBHist
                (twinSubstrateBoundaryClassifierEncodeBHist N))) =
          some (TwinSubstrateBoundaryClassifierUp.mk M G Q L D H C P N)
      rw [twinSubstrateBoundaryClassifierDecode_encode_bhist M,
        twinSubstrateBoundaryClassifierDecode_encode_bhist G,
        twinSubstrateBoundaryClassifierDecode_encode_bhist Q,
        twinSubstrateBoundaryClassifierDecode_encode_bhist L,
        twinSubstrateBoundaryClassifierDecode_encode_bhist D,
        twinSubstrateBoundaryClassifierDecode_encode_bhist H,
        twinSubstrateBoundaryClassifierDecode_encode_bhist C,
        twinSubstrateBoundaryClassifierDecode_encode_bhist P,
        twinSubstrateBoundaryClassifierDecode_encode_bhist N]

private theorem twinSubstrateBoundaryClassifierToEventFlow_injective
    {x y : TwinSubstrateBoundaryClassifierUp} :
    twinSubstrateBoundaryClassifierToEventFlow x =
      twinSubstrateBoundaryClassifierToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      twinSubstrateBoundaryClassifierFromEventFlow
          (twinSubstrateBoundaryClassifierToEventFlow x) =
        twinSubstrateBoundaryClassifierFromEventFlow
          (twinSubstrateBoundaryClassifierToEventFlow y) :=
    congrArg twinSubstrateBoundaryClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (twinSubstrateBoundaryClassifier_round_trip x).symm
      (Eq.trans hread (twinSubstrateBoundaryClassifier_round_trip y)))

private theorem twinSubstrateBoundaryClassifier_field_faithful :
    forall x y : TwinSubstrateBoundaryClassifierUp,
      twinSubstrateBoundaryClassifierFields x =
        twinSubstrateBoundaryClassifierFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 G1 Q1 L1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 G2 Q2 L2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance twinSubstrateBoundaryClassifierBHistCarrier :
    BHistCarrier TwinSubstrateBoundaryClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := twinSubstrateBoundaryClassifierToEventFlow
  fromEventFlow := twinSubstrateBoundaryClassifierFromEventFlow

instance twinSubstrateBoundaryClassifierChapterTasteGate :
    ChapterTasteGate TwinSubstrateBoundaryClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      twinSubstrateBoundaryClassifierFromEventFlow
          (twinSubstrateBoundaryClassifierToEventFlow x) =
        some x
    exact twinSubstrateBoundaryClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (twinSubstrateBoundaryClassifierToEventFlow_injective heq)

instance twinSubstrateBoundaryClassifierFieldFaithful :
    FieldFaithful TwinSubstrateBoundaryClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := twinSubstrateBoundaryClassifierFields
  field_faithful := twinSubstrateBoundaryClassifier_field_faithful

instance twinSubstrateBoundaryClassifierNontrivial :
    Nontrivial TwinSubstrateBoundaryClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TwinSubstrateBoundaryClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TwinSubstrateBoundaryClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TwinSubstrateBoundaryClassifierTasteGate_single_carrier_alignment :
    (forall h : BHist,
      twinSubstrateBoundaryClassifierDecodeBHist
        (twinSubstrateBoundaryClassifierEncodeBHist h) = h) ∧
      (forall x : TwinSubstrateBoundaryClassifierUp,
        twinSubstrateBoundaryClassifierFromEventFlow
          (twinSubstrateBoundaryClassifierToEventFlow x) = some x) ∧
        (forall x y : TwinSubstrateBoundaryClassifierUp,
          twinSubstrateBoundaryClassifierToEventFlow x =
            twinSubstrateBoundaryClassifierToEventFlow y -> x = y) ∧
          twinSubstrateBoundaryClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact twinSubstrateBoundaryClassifierDecode_encode_bhist
  · constructor
    · exact twinSubstrateBoundaryClassifier_round_trip
    · constructor
      · intro x y heq
        exact twinSubstrateBoundaryClassifierToEventFlow_injective heq
      · rfl

end BEDC.Derived.TwinSubstrateBoundaryClassifierUp
