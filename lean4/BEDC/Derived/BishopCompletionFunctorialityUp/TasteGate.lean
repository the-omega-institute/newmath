import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionFunctorialityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionFunctorialityUp : Type where
  | mk (S T U L E Q R W H C P N : BHist) : BishopCompletionFunctorialityUp
  deriving DecidableEq

def bishopCompletionFunctorialityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionFunctorialityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionFunctorialityEncodeBHist h

def bishopCompletionFunctorialityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionFunctorialityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionFunctorialityDecodeBHist tail)

private theorem bishopCompletionFunctoriality_decode_encode_bhist :
    ∀ h : BHist,
      bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionFunctorialityFields :
    BishopCompletionFunctorialityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionFunctorialityUp.mk S T U L E Q R W H C P N =>
      [S, T, U, L, E, Q, R, W, H, C, P, N]

private def bishopCompletionFunctorialityToEventFlow :
    BishopCompletionFunctorialityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCompletionFunctorialityFields x).map bishopCompletionFunctorialityEncodeBHist

private def bishopCompletionFunctorialityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionFunctorialityEventAt index rest

private def bishopCompletionFunctorialityFromEventFlow (ef : EventFlow) :
    Option BishopCompletionFunctorialityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCompletionFunctorialityUp.mk
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 0 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 1 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 2 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 3 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 4 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 5 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 6 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 7 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 8 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 9 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 10 ef))
      (bishopCompletionFunctorialityDecodeBHist
        (bishopCompletionFunctorialityEventAt 11 ef)))

private theorem bishopCompletionFunctoriality_round_trip
    (x : BishopCompletionFunctorialityUp) :
    bishopCompletionFunctorialityFromEventFlow
      (bishopCompletionFunctorialityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T U L E Q R W H C P N =>
      change
        some
          (BishopCompletionFunctorialityUp.mk
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist S))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist T))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist U))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist L))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist E))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist Q))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist R))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist W))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist H))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist C))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist P))
            (bishopCompletionFunctorialityDecodeBHist
              (bishopCompletionFunctorialityEncodeBHist N))) =
          some (BishopCompletionFunctorialityUp.mk S T U L E Q R W H C P N)
      rw [bishopCompletionFunctoriality_decode_encode_bhist S,
        bishopCompletionFunctoriality_decode_encode_bhist T,
        bishopCompletionFunctoriality_decode_encode_bhist U,
        bishopCompletionFunctoriality_decode_encode_bhist L,
        bishopCompletionFunctoriality_decode_encode_bhist E,
        bishopCompletionFunctoriality_decode_encode_bhist Q,
        bishopCompletionFunctoriality_decode_encode_bhist R,
        bishopCompletionFunctoriality_decode_encode_bhist W,
        bishopCompletionFunctoriality_decode_encode_bhist H,
        bishopCompletionFunctoriality_decode_encode_bhist C,
        bishopCompletionFunctoriality_decode_encode_bhist P,
        bishopCompletionFunctoriality_decode_encode_bhist N]

private theorem bishopCompletionFunctorialityToEventFlow_injective
    {x y : BishopCompletionFunctorialityUp} :
    bishopCompletionFunctorialityToEventFlow x =
      bishopCompletionFunctorialityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionFunctorialityFromEventFlow
          (bishopCompletionFunctorialityToEventFlow x) =
        bishopCompletionFunctorialityFromEventFlow
          (bishopCompletionFunctorialityToEventFlow y) :=
    congrArg bishopCompletionFunctorialityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompletionFunctoriality_round_trip x).symm
      (Eq.trans hread (bishopCompletionFunctoriality_round_trip y)))

private theorem bishopCompletionFunctoriality_field_faithful :
    ∀ x y : BishopCompletionFunctorialityUp,
      bishopCompletionFunctorialityFields x =
        bishopCompletionFunctorialityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S T U L E Q R W H C P N =>
      cases y with
      | mk S' T' U' L' E' Q' R' W' H' C' P' N' =>
          change
            [S, T, U, L, E, Q, R, W, H, C, P, N] =
              [S', T', U', L', E', Q', R', W', H', C', P', N'] at hfields
          injection hfields with hS hTail0
          injection hTail0 with hT hTail1
          injection hTail1 with hU hTail2
          injection hTail2 with hL hTail3
          injection hTail3 with hE hTail4
          injection hTail4 with hQ hTail5
          injection hTail5 with hR hTail6
          injection hTail6 with hW hTail7
          injection hTail7 with hH hTail8
          injection hTail8 with hC hTail9
          injection hTail9 with hP hTail10
          injection hTail10 with hN _hNil
          cases hS
          cases hT
          cases hU
          cases hL
          cases hE
          cases hQ
          cases hR
          cases hW
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance bishopCompletionFunctorialityBHistCarrier :
    BHistCarrier BishopCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionFunctorialityToEventFlow
  fromEventFlow := bishopCompletionFunctorialityFromEventFlow

instance bishopCompletionFunctorialityChapterTasteGate :
    ChapterTasteGate BishopCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionFunctorialityFromEventFlow
        (bishopCompletionFunctorialityToEventFlow x) = some x
    exact bishopCompletionFunctoriality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompletionFunctorialityToEventFlow_injective heq)

instance bishopCompletionFunctorialityFieldFaithful :
    FieldFaithful BishopCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompletionFunctorialityFields
  field_faithful := bishopCompletionFunctoriality_field_faithful

instance bishopCompletionFunctorialityNontrivial :
    Nontrivial BishopCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompletionFunctorialityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BishopCompletionFunctorialityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopCompletionFunctorialityNameCertObligations
    (x : BishopCompletionFunctorialityUp) :
    (∃ S T U L E Q R W H C P N : BHist,
      x = BishopCompletionFunctorialityUp.mk S T U L E Q R W H C P N ∧
        bishopCompletionFunctorialityFields x = [S, T, U, L, E, Q, R, W, H, C, P, N] ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      bishopCompletionFunctorialityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T U L E Q R W H C P N =>
      constructor
      · refine ⟨S, T, U, L, E, Q, R, W, H, C, P, N, rfl, rfl, ?_⟩
        change
          bishopCompletionFunctorialityFromEventFlow
              (bishopCompletionFunctorialityToEventFlow
                (BishopCompletionFunctorialityUp.mk S T U L E Q R W H C P N)) =
            some (BishopCompletionFunctorialityUp.mk S T U L E Q R W H C P N)
        exact
          bishopCompletionFunctoriality_round_trip
            (BishopCompletionFunctorialityUp.mk S T U L E Q R W H C P N)
      · rfl

end BEDC.Derived.BishopCompletionFunctorialityUp
