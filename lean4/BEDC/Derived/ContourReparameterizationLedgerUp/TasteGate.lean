import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContourReparameterizationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContourReparameterizationLedgerUp : Type where
  | mk (G G' U F S M I H C P N : BHist) : ContourReparameterizationLedgerUp

def contourReparameterizationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contourReparameterizationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contourReparameterizationLedgerEncodeBHist h

def contourReparameterizationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contourReparameterizationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contourReparameterizationLedgerDecodeBHist tail)

private theorem contourReparameterizationLedger_decode_encode_bhist :
    ∀ h : BHist,
      contourReparameterizationLedgerDecodeBHist
        (contourReparameterizationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def contourReparameterizationLedgerFields :
    ContourReparameterizationLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContourReparameterizationLedgerUp.mk G G' U F S M I H C P N =>
      [G, G', U, F, S, M, I, H, C, P, N]

def contourReparameterizationLedgerToEventFlow :
    ContourReparameterizationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (contourReparameterizationLedgerFields x).map
        contourReparameterizationLedgerEncodeBHist

private def contourReparameterizationLedgerEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      contourReparameterizationLedgerEventAtDefault index rest

def contourReparameterizationLedgerFromEventFlow :
    EventFlow → Option ContourReparameterizationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ContourReparameterizationLedgerUp.mk
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 0 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 1 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 2 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 3 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 4 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 5 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 6 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 7 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 8 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 9 ef))
          (contourReparameterizationLedgerDecodeBHist
            (contourReparameterizationLedgerEventAtDefault 10 ef)))

private theorem contourReparameterizationLedger_round_trip :
    ∀ x : ContourReparameterizationLedgerUp,
      contourReparameterizationLedgerFromEventFlow
          (contourReparameterizationLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G G' U F S M I H C P N =>
      change
        some
          (ContourReparameterizationLedgerUp.mk
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist G))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist G'))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist U))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist F))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist S))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist M))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist I))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist H))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist C))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist P))
            (contourReparameterizationLedgerDecodeBHist
              (contourReparameterizationLedgerEncodeBHist N))) =
          some (ContourReparameterizationLedgerUp.mk G G' U F S M I H C P N)
      rw [contourReparameterizationLedger_decode_encode_bhist G,
        contourReparameterizationLedger_decode_encode_bhist G',
        contourReparameterizationLedger_decode_encode_bhist U,
        contourReparameterizationLedger_decode_encode_bhist F,
        contourReparameterizationLedger_decode_encode_bhist S,
        contourReparameterizationLedger_decode_encode_bhist M,
        contourReparameterizationLedger_decode_encode_bhist I,
        contourReparameterizationLedger_decode_encode_bhist H,
        contourReparameterizationLedger_decode_encode_bhist C,
        contourReparameterizationLedger_decode_encode_bhist P,
        contourReparameterizationLedger_decode_encode_bhist N]

private theorem contourReparameterizationLedgerToEventFlow_injective
    {x y : ContourReparameterizationLedgerUp} :
    contourReparameterizationLedgerToEventFlow x =
        contourReparameterizationLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contourReparameterizationLedgerFromEventFlow
          (contourReparameterizationLedgerToEventFlow x) =
        contourReparameterizationLedgerFromEventFlow
          (contourReparameterizationLedgerToEventFlow y) :=
    congrArg contourReparameterizationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (contourReparameterizationLedger_round_trip x).symm
      (Eq.trans hread (contourReparameterizationLedger_round_trip y)))

instance contourReparameterizationLedgerBHistCarrier :
    BHistCarrier ContourReparameterizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contourReparameterizationLedgerToEventFlow
  fromEventFlow := contourReparameterizationLedgerFromEventFlow

instance contourReparameterizationLedgerChapterTasteGate :
    ChapterTasteGate ContourReparameterizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      contourReparameterizationLedgerFromEventFlow
          (contourReparameterizationLedgerToEventFlow x) =
        some x
    exact contourReparameterizationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contourReparameterizationLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ContourReparameterizationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contourReparameterizationLedgerChapterTasteGate

theorem ContourReparameterizationLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        contourReparameterizationLedgerDecodeBHist
          (contourReparameterizationLedgerEncodeBHist h) = h) ∧
      (∀ x : ContourReparameterizationLedgerUp,
        contourReparameterizationLedgerFromEventFlow
            (contourReparameterizationLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : ContourReparameterizationLedgerUp,
          contourReparameterizationLedgerToEventFlow x =
              contourReparameterizationLedgerToEventFlow y →
            x = y) ∧
          contourReparameterizationLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨contourReparameterizationLedger_decode_encode_bhist,
      contourReparameterizationLedger_round_trip,
      fun x y => contourReparameterizationLedgerToEventFlow_injective (x := x) (y := y),
      rfl⟩

end BEDC.Derived.ContourReparameterizationLedgerUp
