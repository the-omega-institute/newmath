import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContourIntegralSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContourIntegralSocketUp : Type where
  | mk (G F M I L H C P N : BHist) : ContourIntegralSocketUp

def contourIntegralSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contourIntegralSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contourIntegralSocketEncodeBHist h

def contourIntegralSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contourIntegralSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contourIntegralSocketDecodeBHist tail)

private theorem ContourIntegralSocketTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contourIntegralSocketFields : ContourIntegralSocketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContourIntegralSocketUp.mk G F M I L H C P N => [G, F, M, I, L, H, C, P, N]

def contourIntegralSocketToEventFlow : ContourIntegralSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (contourIntegralSocketFields x).map contourIntegralSocketEncodeBHist

private def contourIntegralSocketEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contourIntegralSocketEventAtDefault index rest

def contourIntegralSocketFromEventFlow :
    EventFlow → Option ContourIntegralSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ContourIntegralSocketUp.mk
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 0 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 1 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 2 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 3 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 4 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 5 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 6 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 7 ef))
          (contourIntegralSocketDecodeBHist (contourIntegralSocketEventAtDefault 8 ef)))

private theorem ContourIntegralSocketTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContourIntegralSocketUp,
      contourIntegralSocketFromEventFlow (contourIntegralSocketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G F M I L H C P N =>
      change
        some
          (ContourIntegralSocketUp.mk
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist G))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist F))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist M))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist I))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist L))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist H))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist C))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist P))
            (contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist N))) =
          some (ContourIntegralSocketUp.mk G F M I L H C P N)
      rw [ContourIntegralSocketTasteGate_single_carrier_alignment_decode G,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode F,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode M,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode I,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode L,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode H,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode C,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode P,
        ContourIntegralSocketTasteGate_single_carrier_alignment_decode N]

private theorem ContourIntegralSocketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContourIntegralSocketUp} :
    contourIntegralSocketToEventFlow x = contourIntegralSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contourIntegralSocketFromEventFlow (contourIntegralSocketToEventFlow x) =
        contourIntegralSocketFromEventFlow (contourIntegralSocketToEventFlow y) :=
    congrArg contourIntegralSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContourIntegralSocketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContourIntegralSocketTasteGate_single_carrier_alignment_round_trip y)))

instance contourIntegralSocketBHistCarrier :
    BHistCarrier ContourIntegralSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contourIntegralSocketToEventFlow
  fromEventFlow := contourIntegralSocketFromEventFlow

instance contourIntegralSocketChapterTasteGate :
    ChapterTasteGate ContourIntegralSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contourIntegralSocketFromEventFlow (contourIntegralSocketToEventFlow x) = some x
    exact ContourIntegralSocketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContourIntegralSocketTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ContourIntegralSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contourIntegralSocketChapterTasteGate

theorem ContourIntegralSocketTasteGate_single_carrier_alignment :
    (∀ h : BHist, contourIntegralSocketDecodeBHist (contourIntegralSocketEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ContourIntegralSocketUp) ∧
        Nonempty (ChapterTasteGate ContourIntegralSocketUp) ∧
          contourIntegralSocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨ContourIntegralSocketTasteGate_single_carrier_alignment_decode,
      ⟨contourIntegralSocketBHistCarrier⟩,
      ⟨contourIntegralSocketChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ContourIntegralSocketUp
