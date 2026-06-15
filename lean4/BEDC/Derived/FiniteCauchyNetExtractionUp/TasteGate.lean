import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCauchyNetExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCauchyNetExtractionUp : Type where
  | mk (D W Q M T E H C P N : BHist) : FiniteCauchyNetExtractionUp
  deriving DecidableEq

def finiteCauchyNetExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCauchyNetExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCauchyNetExtractionEncodeBHist h

def finiteCauchyNetExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCauchyNetExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCauchyNetExtractionDecodeBHist tail)

private theorem finiteCauchyNetExtractionDecode_encode :
    ∀ h : BHist,
      finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCauchyNetExtractionFields :
    FiniteCauchyNetExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCauchyNetExtractionUp.mk D W Q M T E H C P N => [D, W, Q, M, T, E, H, C, P, N]

def finiteCauchyNetExtractionToEventFlow :
    FiniteCauchyNetExtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteCauchyNetExtractionFields x).map finiteCauchyNetExtractionEncodeBHist

private def finiteCauchyNetExtractionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCauchyNetExtractionEventAt index rest

def finiteCauchyNetExtractionFromEventFlow :
    EventFlow → Option FiniteCauchyNetExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FiniteCauchyNetExtractionUp.mk
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 0 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 1 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 2 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 3 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 4 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 5 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 6 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 7 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 8 ef))
        (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEventAt 9 ef)))

private theorem finiteCauchyNetExtraction_round_trip
    (x : FiniteCauchyNetExtractionUp) :
    finiteCauchyNetExtractionFromEventFlow (finiteCauchyNetExtractionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W Q M T E H C P N =>
      change
        some
          (FiniteCauchyNetExtractionUp.mk
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist D))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist W))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist Q))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist M))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist T))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist E))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist H))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist C))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist P))
            (finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist N))) =
          some (FiniteCauchyNetExtractionUp.mk D W Q M T E H C P N)
      rw [finiteCauchyNetExtractionDecode_encode D, finiteCauchyNetExtractionDecode_encode W,
        finiteCauchyNetExtractionDecode_encode Q, finiteCauchyNetExtractionDecode_encode M,
        finiteCauchyNetExtractionDecode_encode T, finiteCauchyNetExtractionDecode_encode E,
        finiteCauchyNetExtractionDecode_encode H, finiteCauchyNetExtractionDecode_encode C,
        finiteCauchyNetExtractionDecode_encode P, finiteCauchyNetExtractionDecode_encode N]

private theorem finiteCauchyNetExtractionToEventFlow_injective
    {x y : FiniteCauchyNetExtractionUp} :
    finiteCauchyNetExtractionToEventFlow x = finiteCauchyNetExtractionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCauchyNetExtractionFromEventFlow (finiteCauchyNetExtractionToEventFlow x) =
        finiteCauchyNetExtractionFromEventFlow (finiteCauchyNetExtractionToEventFlow y) :=
    congrArg finiteCauchyNetExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteCauchyNetExtraction_round_trip x).symm
      (Eq.trans hread (finiteCauchyNetExtraction_round_trip y)))

instance finiteCauchyNetExtractionBHistCarrier :
    BHistCarrier FiniteCauchyNetExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCauchyNetExtractionToEventFlow
  fromEventFlow := finiteCauchyNetExtractionFromEventFlow

instance finiteCauchyNetExtractionChapterTasteGate :
    ChapterTasteGate FiniteCauchyNetExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteCauchyNetExtractionFromEventFlow (finiteCauchyNetExtractionToEventFlow x) =
        some x
    exact finiteCauchyNetExtraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteCauchyNetExtractionToEventFlow_injective heq)

theorem FiniteCauchyNetExtractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteCauchyNetExtractionDecodeBHist (finiteCauchyNetExtractionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteCauchyNetExtractionUp) ∧
      Nonempty (ChapterTasteGate FiniteCauchyNetExtractionUp) ∧
      finiteCauchyNetExtractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨finiteCauchyNetExtractionDecode_encode,
      ⟨finiteCauchyNetExtractionBHistCarrier⟩,
      ⟨finiteCauchyNetExtractionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteCauchyNetExtractionUp
