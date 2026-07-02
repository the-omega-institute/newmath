import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyCompletionPairUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyCompletionPairUp : Type where
  | mk (M D W R T E H C P N : BHist) : BishopCauchyCompletionPairUp
  deriving DecidableEq

def bishopCauchyCompletionPairFields : BishopCauchyCompletionPairUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyCompletionPairUp.mk M D W R T E H C P N =>
      [M, D, W, R, T, E, H, C, P, N]

def bishopCauchyCompletionPairEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyCompletionPairEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyCompletionPairEncodeBHist h

def bishopCauchyCompletionPairDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyCompletionPairDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyCompletionPairDecodeBHist tail)

private theorem bishopCauchyCompletionPair_decode_encode (h : BHist) :
    bishopCauchyCompletionPairDecodeBHist (bishopCauchyCompletionPairEncodeBHist h) =
      h := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyCompletionPairToEventFlow :
    BishopCauchyCompletionPairUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCauchyCompletionPairFields x).map bishopCauchyCompletionPairEncodeBHist

private def bishopCauchyCompletionPairEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopCauchyCompletionPairEventAtDefault index rest

def bishopCauchyCompletionPairFromEventFlow
    (ef : EventFlow) : Option BishopCauchyCompletionPairUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyCompletionPairUp.mk
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 0 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 1 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 2 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 3 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 4 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 5 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 6 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 7 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 8 ef))
      (bishopCauchyCompletionPairDecodeBHist
        (bishopCauchyCompletionPairEventAtDefault 9 ef)))

private theorem bishopCauchyCompletionPair_round_trip
    (x : BishopCauchyCompletionPairUp) :
    bishopCauchyCompletionPairFromEventFlow
        (bishopCauchyCompletionPairToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M D W R T E H C P N =>
      change
        some
          (BishopCauchyCompletionPairUp.mk
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist M))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist D))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist W))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist R))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist T))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist E))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist H))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist C))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist P))
            (bishopCauchyCompletionPairDecodeBHist
              (bishopCauchyCompletionPairEncodeBHist N))) =
          some (BishopCauchyCompletionPairUp.mk M D W R T E H C P N)
      rw [bishopCauchyCompletionPair_decode_encode M,
        bishopCauchyCompletionPair_decode_encode D,
        bishopCauchyCompletionPair_decode_encode W,
        bishopCauchyCompletionPair_decode_encode R,
        bishopCauchyCompletionPair_decode_encode T,
        bishopCauchyCompletionPair_decode_encode E,
        bishopCauchyCompletionPair_decode_encode H,
        bishopCauchyCompletionPair_decode_encode C,
        bishopCauchyCompletionPair_decode_encode P,
        bishopCauchyCompletionPair_decode_encode N]

private theorem bishopCauchyCompletionPairToEventFlow_injective
    {x y : BishopCauchyCompletionPairUp} :
    bishopCauchyCompletionPairToEventFlow x =
      bishopCauchyCompletionPairToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyCompletionPairFromEventFlow
          (bishopCauchyCompletionPairToEventFlow x) =
        bishopCauchyCompletionPairFromEventFlow
          (bishopCauchyCompletionPairToEventFlow y) :=
    congrArg bishopCauchyCompletionPairFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (bishopCauchyCompletionPair_round_trip x).symm
      (Eq.trans hread (bishopCauchyCompletionPair_round_trip y)))

instance bishopCauchyCompletionPairBHistCarrier :
    BHistCarrier BishopCauchyCompletionPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyCompletionPairToEventFlow
  fromEventFlow := bishopCauchyCompletionPairFromEventFlow

instance bishopCauchyCompletionPairChapterTasteGate :
    ChapterTasteGate BishopCauchyCompletionPairUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyCompletionPairFromEventFlow
        (bishopCauchyCompletionPairToEventFlow x) = some x
    exact bishopCauchyCompletionPair_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyCompletionPairToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCauchyCompletionPairUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyCompletionPairChapterTasteGate

theorem BishopCauchyCompletionPairCarrier_namecert_obligations
    (x : BishopCauchyCompletionPairUp) :
    ∃ metric dense windows regular tolerance sealRow transportRow replay provenance localName
        sourceRoute cauchyRoute sealRoute structuralRoute : BHist,
      x =
          BishopCauchyCompletionPairUp.mk metric dense windows regular tolerance sealRow
            transportRow replay provenance localName ∧
        Cont metric dense sourceRoute ∧
          Cont windows regular cauchyRoute ∧
            Cont tolerance sealRow sealRoute ∧
              Cont transportRow replay structuralRoute ∧
                bishopCauchyCompletionPairFromEventFlow
                    (bishopCauchyCompletionPairToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M D W R T E H C P N =>
      refine ⟨M, D, W, R, T, E, H, C, P, N, append M D, append W R,
        append T E, append H C, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      · exact bishopCauchyCompletionPair_round_trip
          (BishopCauchyCompletionPairUp.mk M D W R T E H C P N)

end BEDC.Derived.BishopCauchyCompletionPairUp
