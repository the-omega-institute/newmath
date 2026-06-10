import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HellyTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HellyTheoremUp : Type where
  | mk (A V F W S I T C P N : BHist) : HellyTheoremUp
  deriving DecidableEq

def hellyTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hellyTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hellyTheoremEncodeBHist h

def hellyTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hellyTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hellyTheoremDecodeBHist tail)

private theorem hellyTheoremDecode_encode_bhist :
    ∀ h : BHist, hellyTheoremDecodeBHist (hellyTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hellyTheoremToEventFlow : HellyTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HellyTheoremUp.mk A V F W S I T C P N =>
      [hellyTheoremEncodeBHist A,
        hellyTheoremEncodeBHist V,
        hellyTheoremEncodeBHist F,
        hellyTheoremEncodeBHist W,
        hellyTheoremEncodeBHist S,
        hellyTheoremEncodeBHist I,
        hellyTheoremEncodeBHist T,
        hellyTheoremEncodeBHist C,
        hellyTheoremEncodeBHist P,
        hellyTheoremEncodeBHist N]

private def hellyTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hellyTheoremEventAtDefault index rest

def hellyTheoremFromEventFlow (ef : EventFlow) : Option HellyTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HellyTheoremUp.mk
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 0 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 1 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 2 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 3 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 4 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 5 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 6 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 7 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 8 ef))
      (hellyTheoremDecodeBHist (hellyTheoremEventAtDefault 9 ef)))

private theorem hellyTheorem_round_trip :
    ∀ x : HellyTheoremUp, hellyTheoremFromEventFlow (hellyTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A V F W S I T C P N =>
      change
        some
            (HellyTheoremUp.mk
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist A))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist V))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist F))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist W))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist S))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist I))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist T))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist C))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist P))
              (hellyTheoremDecodeBHist (hellyTheoremEncodeBHist N))) =
          some (HellyTheoremUp.mk A V F W S I T C P N)
      rw [hellyTheoremDecode_encode_bhist A, hellyTheoremDecode_encode_bhist V,
        hellyTheoremDecode_encode_bhist F, hellyTheoremDecode_encode_bhist W,
        hellyTheoremDecode_encode_bhist S, hellyTheoremDecode_encode_bhist I,
        hellyTheoremDecode_encode_bhist T, hellyTheoremDecode_encode_bhist C,
        hellyTheoremDecode_encode_bhist P, hellyTheoremDecode_encode_bhist N]

private theorem hellyTheoremToEventFlow_injective {x y : HellyTheoremUp} :
    hellyTheoremToEventFlow x = hellyTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hellyTheoremFromEventFlow (hellyTheoremToEventFlow x) =
        hellyTheoremFromEventFlow (hellyTheoremToEventFlow y) :=
    congrArg hellyTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hellyTheorem_round_trip x).symm
      (Eq.trans hread (hellyTheorem_round_trip y)))

instance hellyTheoremBHistCarrier : BHistCarrier HellyTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hellyTheoremToEventFlow
  fromEventFlow := hellyTheoremFromEventFlow

instance hellyTheoremChapterTasteGate : ChapterTasteGate HellyTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hellyTheoremFromEventFlow (hellyTheoremToEventFlow x) = some x
    exact hellyTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hellyTheoremToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HellyTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hellyTheoremChapterTasteGate

theorem HellyTheoremTasteGate_single_carrier_alignment :
    ChapterTasteGate HellyTheoremUp ∧
      (∀ h : BHist, hellyTheoremDecodeBHist (hellyTheoremEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨hellyTheoremChapterTasteGate, hellyTheoremDecode_encode_bhist⟩

end BEDC.Derived.HellyTheoremUp
