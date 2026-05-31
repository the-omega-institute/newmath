import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArzelaAscoliFiniteEquicontinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArzelaAscoliFiniteEquicontinuousUp : Type where
  | mk (K E U M D W Q L S H C P N : BHist) : ArzelaAscoliFiniteEquicontinuousUp
  deriving DecidableEq

def arzelaAscoliFiniteEquicontinuousEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arzelaAscoliFiniteEquicontinuousEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arzelaAscoliFiniteEquicontinuousEncodeBHist h

def arzelaAscoliFiniteEquicontinuousDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arzelaAscoliFiniteEquicontinuousDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arzelaAscoliFiniteEquicontinuousDecodeBHist tail)

private theorem ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      arzelaAscoliFiniteEquicontinuousDecodeBHist
        (arzelaAscoliFiniteEquicontinuousEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def arzelaAscoliFiniteEquicontinuousFields :
    ArzelaAscoliFiniteEquicontinuousUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArzelaAscoliFiniteEquicontinuousUp.mk K E U M D W Q L S H C P N =>
      [K, E, U, M, D, W, Q, L, S, H, C, P, N]

def arzelaAscoliFiniteEquicontinuousToEventFlow :
    ArzelaAscoliFiniteEquicontinuousUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (arzelaAscoliFiniteEquicontinuousFields x).map
      arzelaAscoliFiniteEquicontinuousEncodeBHist

private def arzelaAscoliFiniteEquicontinuousEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      arzelaAscoliFiniteEquicontinuousEventAtDefault index rest

def arzelaAscoliFiniteEquicontinuousFromEventFlow :
    EventFlow → Option ArzelaAscoliFiniteEquicontinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ArzelaAscoliFiniteEquicontinuousUp.mk
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 0 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 1 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 2 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 3 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 4 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 5 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 6 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 7 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 8 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 9 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 10 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 11 ef))
        (arzelaAscoliFiniteEquicontinuousDecodeBHist
          (arzelaAscoliFiniteEquicontinuousEventAtDefault 12 ef)))

private theorem ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArzelaAscoliFiniteEquicontinuousUp,
      arzelaAscoliFiniteEquicontinuousFromEventFlow
        (arzelaAscoliFiniteEquicontinuousToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K E U M D W Q L S H C P N =>
      change
        some
          (ArzelaAscoliFiniteEquicontinuousUp.mk
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist K))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist E))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist U))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist M))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist D))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist W))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist Q))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist L))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist S))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist H))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist C))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist P))
            (arzelaAscoliFiniteEquicontinuousDecodeBHist
              (arzelaAscoliFiniteEquicontinuousEncodeBHist N))) =
          some (ArzelaAscoliFiniteEquicontinuousUp.mk K E U M D W Q L S H C P N)
      rw [ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode K,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode E,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode U,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode M,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode D,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode W,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode Q,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode L,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode S,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode H,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode C,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode P,
        ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode N]

private theorem ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArzelaAscoliFiniteEquicontinuousUp} :
    arzelaAscoliFiniteEquicontinuousToEventFlow x =
      arzelaAscoliFiniteEquicontinuousToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arzelaAscoliFiniteEquicontinuousFromEventFlow
          (arzelaAscoliFiniteEquicontinuousToEventFlow x) =
        arzelaAscoliFiniteEquicontinuousFromEventFlow
          (arzelaAscoliFiniteEquicontinuousToEventFlow y) :=
    congrArg arzelaAscoliFiniteEquicontinuousFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_round_trip y)))

instance arzelaAscoliFiniteEquicontinuousBHistCarrier :
    BHistCarrier ArzelaAscoliFiniteEquicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arzelaAscoliFiniteEquicontinuousToEventFlow
  fromEventFlow := arzelaAscoliFiniteEquicontinuousFromEventFlow

instance arzelaAscoliFiniteEquicontinuousChapterTasteGate :
    ChapterTasteGate ArzelaAscoliFiniteEquicontinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      arzelaAscoliFiniteEquicontinuousFromEventFlow
        (arzelaAscoliFiniteEquicontinuousToEventFlow x) = some x
    exact ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate ArzelaAscoliFiniteEquicontinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  arzelaAscoliFiniteEquicontinuousChapterTasteGate

theorem ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      arzelaAscoliFiniteEquicontinuousDecodeBHist
        (arzelaAscoliFiniteEquicontinuousEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ArzelaAscoliFiniteEquicontinuousUp) ∧
        Nonempty (ChapterTasteGate ArzelaAscoliFiniteEquicontinuousUp) ∧
          arzelaAscoliFiniteEquicontinuousEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ArzelaAscoliFiniteEquicontinuousTasteGate_single_carrier_alignment_decode,
      ⟨arzelaAscoliFiniteEquicontinuousBHistCarrier⟩,
      ⟨arzelaAscoliFiniteEquicontinuousChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ArzelaAscoliFiniteEquicontinuousUp
