import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformRadiusLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformRadiusLedgerUp : Type where
  | mk (K M G F R U H C P N : BHist) : CompactUniformRadiusLedgerUp
  deriving DecidableEq

def compactUniformRadiusLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformRadiusLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformRadiusLedgerEncodeBHist h

def compactUniformRadiusLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformRadiusLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformRadiusLedgerDecodeBHist tail)

private theorem compactUniformRadiusLedger_decode_encode :
    ∀ h : BHist,
      compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformRadiusLedgerFields : CompactUniformRadiusLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformRadiusLedgerUp.mk K M G F R U H C P N => [K, M, G, F, R, U, H, C, P, N]

def compactUniformRadiusLedgerToEventFlow : CompactUniformRadiusLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformRadiusLedgerFields x).map compactUniformRadiusLedgerEncodeBHist

private def compactUniformRadiusLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformRadiusLedgerEventAtDefault index rest

def compactUniformRadiusLedgerFromEventFlow
    (ef : EventFlow) : Option CompactUniformRadiusLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformRadiusLedgerUp.mk
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 0 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 1 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 2 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 3 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 4 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 5 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 6 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 7 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 8 ef))
      (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEventAtDefault 9 ef)))

private theorem compactUniformRadiusLedger_round_trip :
    ∀ x : CompactUniformRadiusLedgerUp,
      compactUniformRadiusLedgerFromEventFlow (compactUniformRadiusLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M G F R U H C P N =>
      change
        some
          (CompactUniformRadiusLedgerUp.mk
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist K))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist M))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist G))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist F))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist R))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist U))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist H))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist C))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist P))
            (compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist N))) =
          some (CompactUniformRadiusLedgerUp.mk K M G F R U H C P N)
      rw [compactUniformRadiusLedger_decode_encode K,
        compactUniformRadiusLedger_decode_encode M,
        compactUniformRadiusLedger_decode_encode G,
        compactUniformRadiusLedger_decode_encode F,
        compactUniformRadiusLedger_decode_encode R,
        compactUniformRadiusLedger_decode_encode U,
        compactUniformRadiusLedger_decode_encode H,
        compactUniformRadiusLedger_decode_encode C,
        compactUniformRadiusLedger_decode_encode P,
        compactUniformRadiusLedger_decode_encode N]

private theorem compactUniformRadiusLedgerToEventFlow_injective
    {x y : CompactUniformRadiusLedgerUp} :
    compactUniformRadiusLedgerToEventFlow x = compactUniformRadiusLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformRadiusLedgerFromEventFlow (compactUniformRadiusLedgerToEventFlow x) =
        compactUniformRadiusLedgerFromEventFlow (compactUniformRadiusLedgerToEventFlow y) :=
    congrArg compactUniformRadiusLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformRadiusLedger_round_trip x).symm
      (Eq.trans hread (compactUniformRadiusLedger_round_trip y)))

instance compactUniformRadiusLedgerBHistCarrier : BHistCarrier CompactUniformRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformRadiusLedgerToEventFlow
  fromEventFlow := compactUniformRadiusLedgerFromEventFlow

instance compactUniformRadiusLedgerChapterTasteGate :
    ChapterTasteGate CompactUniformRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformRadiusLedgerFromEventFlow (compactUniformRadiusLedgerToEventFlow x) =
      some x
    exact compactUniformRadiusLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformRadiusLedgerToEventFlow_injective heq)

theorem CompactUniformRadiusLedgerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactUniformRadiusLedgerUp) ∧
      (∀ h : BHist,
        compactUniformRadiusLedgerDecodeBHist (compactUniformRadiusLedgerEncodeBHist h) = h) ∧
        (∀ x : CompactUniformRadiusLedgerUp,
          compactUniformRadiusLedgerFromEventFlow (compactUniformRadiusLedgerToEventFlow x) =
            some x) ∧
          compactUniformRadiusLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨compactUniformRadiusLedgerChapterTasteGate⟩,
      compactUniformRadiusLedger_decode_encode,
      compactUniformRadiusLedger_round_trip,
      rfl⟩

end BEDC.Derived.CompactUniformRadiusLedgerUp
