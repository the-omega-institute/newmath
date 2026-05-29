import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorIntersectionTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorIntersectionTheoremUp : Type where
  | mk (Q I L D W R E H C P N : BHist) : CantorIntersectionTheoremUp
  deriving DecidableEq

def cantorIntersectionTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorIntersectionTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorIntersectionTheoremEncodeBHist h

def cantorIntersectionTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorIntersectionTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorIntersectionTheoremDecodeBHist tail)

private theorem CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorIntersectionTheoremFields : CantorIntersectionTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorIntersectionTheoremUp.mk Q I L D W R E H C P N => [Q, I, L, D, W, R, E, H, C, P, N]

def cantorIntersectionTheoremToEventFlow : CantorIntersectionTheoremUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cantorIntersectionTheoremFields x).map cantorIntersectionTheoremEncodeBHist

private def cantorIntersectionTheoremEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorIntersectionTheoremEventAtDefault index rest

def cantorIntersectionTheoremFromEventFlow
    (ef : EventFlow) : Option CantorIntersectionTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CantorIntersectionTheoremUp.mk
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 0 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 1 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 2 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 3 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 4 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 5 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 6 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 7 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 8 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 9 ef))
      (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEventAtDefault 10 ef)))

private theorem CantorIntersectionTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : CantorIntersectionTheoremUp,
      cantorIntersectionTheoremFromEventFlow (cantorIntersectionTheoremToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q I L D W R E H C P N =>
      change
        some
          (CantorIntersectionTheoremUp.mk
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist Q))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist I))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist L))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist D))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist W))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist R))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist E))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist H))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist C))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist P))
            (cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist N))) =
          some (CantorIntersectionTheoremUp.mk Q I L D W R E H C P N)
      rw [CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode Q,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode I,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode L,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode D,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode W,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode R,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode E,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode H,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode C,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode P,
        CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode N]

private theorem CantorIntersectionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CantorIntersectionTheoremUp} :
    cantorIntersectionTheoremToEventFlow x = cantorIntersectionTheoremToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorIntersectionTheoremFromEventFlow (cantorIntersectionTheoremToEventFlow x) =
        cantorIntersectionTheoremFromEventFlow (cantorIntersectionTheoremToEventFlow y) :=
    congrArg cantorIntersectionTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CantorIntersectionTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CantorIntersectionTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance cantorIntersectionTheoremBHistCarrier :
    BHistCarrier CantorIntersectionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorIntersectionTheoremToEventFlow
  fromEventFlow := cantorIntersectionTheoremFromEventFlow

instance cantorIntersectionTheoremChapterTasteGate :
    ChapterTasteGate CantorIntersectionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cantorIntersectionTheoremFromEventFlow (cantorIntersectionTheoremToEventFlow x) =
        some x
    exact CantorIntersectionTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorIntersectionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CantorIntersectionTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorIntersectionTheoremChapterTasteGate

theorem CantorIntersectionTheoremTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cantorIntersectionTheoremDecodeBHist (cantorIntersectionTheoremEncodeBHist h) = h) /\
      Nonempty (BHistCarrier CantorIntersectionTheoremUp) /\
        Nonempty (ChapterTasteGate CantorIntersectionTheoremUp) /\
          cantorIntersectionTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CantorIntersectionTheoremTasteGate_single_carrier_alignment_decode,
      ⟨cantorIntersectionTheoremBHistCarrier⟩,
      ⟨cantorIntersectionTheoremChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CantorIntersectionTheoremUp
