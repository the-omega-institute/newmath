import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCauchySandwichUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCauchySandwichUp : Type where
  | mk (L U I W R E H C P N : BHist) : DedekindCauchySandwichUp
  deriving DecidableEq

def dedekindCauchySandwichEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCauchySandwichEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCauchySandwichEncodeBHist h

def dedekindCauchySandwichDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCauchySandwichDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCauchySandwichDecodeBHist tail)

private theorem dedekindCauchySandwich_decode_encode :
    ∀ h : BHist,
      dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dedekindCauchySandwichFields : DedekindCauchySandwichUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCauchySandwichUp.mk L U I W R E H C P N => [L, U, I, W, R, E, H, C, P, N]

def dedekindCauchySandwichToEventFlow : DedekindCauchySandwichUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map dedekindCauchySandwichEncodeBHist (dedekindCauchySandwichFields x)

private def dedekindCauchySandwichRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dedekindCauchySandwichRawAt index rest

def dedekindCauchySandwichFromEventFlow (flow : EventFlow) :
    Option DedekindCauchySandwichUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DedekindCauchySandwichUp.mk
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 0 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 1 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 2 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 3 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 4 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 5 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 6 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 7 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 8 flow))
      (dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichRawAt 9 flow)))

private theorem DedekindCauchySandwichTasteGate_single_carrier_alignment_round_trip
    (x : DedekindCauchySandwichUp) :
    dedekindCauchySandwichFromEventFlow (dedekindCauchySandwichToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U I W R E H C P N =>
      change
        some
            (DedekindCauchySandwichUp.mk
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist L))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist U))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist I))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist W))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist R))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist E))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist H))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist C))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist P))
              (dedekindCauchySandwichDecodeBHist
                (dedekindCauchySandwichEncodeBHist N))) =
          some (DedekindCauchySandwichUp.mk L U I W R E H C P N)
      rw [dedekindCauchySandwich_decode_encode L,
        dedekindCauchySandwich_decode_encode U,
        dedekindCauchySandwich_decode_encode I,
        dedekindCauchySandwich_decode_encode W,
        dedekindCauchySandwich_decode_encode R,
        dedekindCauchySandwich_decode_encode E,
        dedekindCauchySandwich_decode_encode H,
        dedekindCauchySandwich_decode_encode C,
        dedekindCauchySandwich_decode_encode P,
        dedekindCauchySandwich_decode_encode N]

private theorem dedekindCauchySandwichToEventFlow_injective
    {x y : DedekindCauchySandwichUp} :
    dedekindCauchySandwichToEventFlow x = dedekindCauchySandwichToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCauchySandwichFromEventFlow (dedekindCauchySandwichToEventFlow x) =
        dedekindCauchySandwichFromEventFlow (dedekindCauchySandwichToEventFlow y) :=
    congrArg dedekindCauchySandwichFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DedekindCauchySandwichTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DedekindCauchySandwichTasteGate_single_carrier_alignment_round_trip y)))

instance dedekindCauchySandwichBHistCarrier : BHistCarrier DedekindCauchySandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCauchySandwichToEventFlow
  fromEventFlow := dedekindCauchySandwichFromEventFlow

instance dedekindCauchySandwichChapterTasteGate :
    ChapterTasteGate DedekindCauchySandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCauchySandwichFromEventFlow (dedekindCauchySandwichToEventFlow x) =
        some x
    exact DedekindCauchySandwichTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCauchySandwichToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DedekindCauchySandwichUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCauchySandwichChapterTasteGate

theorem DedekindCauchySandwichTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        dedekindCauchySandwichDecodeBHist (dedekindCauchySandwichEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DedekindCauchySandwichUp) ∧
        Nonempty (ChapterTasteGate DedekindCauchySandwichUp) ∧
          dedekindCauchySandwichEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨dedekindCauchySandwich_decode_encode,
      Nonempty.intro dedekindCauchySandwichBHistCarrier,
      Nonempty.intro dedekindCauchySandwichChapterTasteGate,
      rfl⟩

end BEDC.Derived.DedekindCauchySandwichUp
