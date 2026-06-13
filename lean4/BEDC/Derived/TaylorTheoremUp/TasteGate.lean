import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TaylorTheoremUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TaylorTheoremUp : Type where
  | mk (D J P R E Q H C G N : BHist) : TaylorTheoremUp
  deriving DecidableEq

def taylorTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: taylorTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: taylorTheoremEncodeBHist h

def taylorTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (taylorTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (taylorTheoremDecodeBHist tail)

private theorem TaylorTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, taylorTheoremDecodeBHist (taylorTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def taylorTheoremToEventFlow : TaylorTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TaylorTheoremUp.mk D J P R E Q H C G N =>
      [taylorTheoremEncodeBHist D,
        taylorTheoremEncodeBHist J,
        taylorTheoremEncodeBHist P,
        taylorTheoremEncodeBHist R,
        taylorTheoremEncodeBHist E,
        taylorTheoremEncodeBHist Q,
        taylorTheoremEncodeBHist H,
        taylorTheoremEncodeBHist C,
        taylorTheoremEncodeBHist G,
        taylorTheoremEncodeBHist N]

private def taylorTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => taylorTheoremEventAtDefault index rest

def taylorTheoremFromEventFlow (ef : EventFlow) : Option TaylorTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TaylorTheoremUp.mk
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 0 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 1 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 2 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 3 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 4 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 5 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 6 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 7 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 8 ef))
      (taylorTheoremDecodeBHist (taylorTheoremEventAtDefault 9 ef)))

private theorem TaylorTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TaylorTheoremUp,
      taylorTheoremFromEventFlow (taylorTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D J P R E Q H C G N =>
      change
        some
          (TaylorTheoremUp.mk
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist D))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist J))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist P))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist R))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist E))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist Q))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist H))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist C))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist G))
            (taylorTheoremDecodeBHist (taylorTheoremEncodeBHist N))) =
          some (TaylorTheoremUp.mk D J P R E Q H C G N)
      rw [TaylorTheoremTasteGate_single_carrier_alignment_decode_encode D,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode J,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode P,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode R,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode E,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode Q,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode H,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode C,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode G,
        TaylorTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem TaylorTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TaylorTheoremUp} :
    taylorTheoremToEventFlow x = taylorTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      taylorTheoremFromEventFlow (taylorTheoremToEventFlow x) =
        taylorTheoremFromEventFlow (taylorTheoremToEventFlow y) :=
    congrArg taylorTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TaylorTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TaylorTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance taylorTheoremBHistCarrier : BHistCarrier TaylorTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := taylorTheoremToEventFlow
  fromEventFlow := taylorTheoremFromEventFlow

instance taylorTheoremChapterTasteGate : ChapterTasteGate TaylorTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change taylorTheoremFromEventFlow (taylorTheoremToEventFlow x) = some x
    exact TaylorTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TaylorTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate TaylorTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  taylorTheoremChapterTasteGate

theorem TaylorTheoremTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier TaylorTheoremUp) ∧
      Nonempty (ChapterTasteGate TaylorTheoremUp) ∧
        (∀ x : TaylorTheoremUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          taylorTheoremEncodeBHist BHist.Empty = ([] : List BMark) ∧
            taylorTheoremDecodeBHist [BMark.b0] = BHist.e0 BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨taylorTheoremBHistCarrier⟩,
      ⟨taylorTheoremChapterTasteGate⟩,
      ChapterTasteGate.round_trip,
      rfl,
      rfl⟩

end BEDC.Derived.TaylorTheoremUp.TasteGate
