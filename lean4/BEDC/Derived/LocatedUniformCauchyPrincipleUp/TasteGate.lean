import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUniformCauchyPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUniformCauchyPrincipleUp : Type where
  | mk (D S R L B E H C P N : BHist) : LocatedUniformCauchyPrincipleUp
  deriving DecidableEq

def locatedUniformCauchyPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUniformCauchyPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUniformCauchyPrincipleEncodeBHist h

def locatedUniformCauchyPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUniformCauchyPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUniformCauchyPrincipleDecodeBHist tail)

private theorem locatedUniformCauchyPrinciple_decode_encode_bhist :
    ∀ h : BHist,
      locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedUniformCauchyPrincipleFields :
    LocatedUniformCauchyPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUniformCauchyPrincipleUp.mk D S R L B E H C P N => [D, S, R, L, B, E, H, C, P, N]

def locatedUniformCauchyPrincipleToEventFlow :
    LocatedUniformCauchyPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedUniformCauchyPrincipleFields x).map locatedUniformCauchyPrincipleEncodeBHist

private def locatedUniformCauchyPrincipleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedUniformCauchyPrincipleEventAtDefault index rest

def locatedUniformCauchyPrincipleFromEventFlow
    (ef : EventFlow) : Option LocatedUniformCauchyPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedUniformCauchyPrincipleUp.mk
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 0 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 1 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 2 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 3 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 4 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 5 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 6 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 7 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 8 ef))
      (locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEventAtDefault 9 ef)))

private theorem locatedUniformCauchyPrinciple_round_trip
    (x : LocatedUniformCauchyPrincipleUp) :
    locatedUniformCauchyPrincipleFromEventFlow
      (locatedUniformCauchyPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R L B E H C P N =>
      change
        some
          (LocatedUniformCauchyPrincipleUp.mk
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist D))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist S))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist R))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist L))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist B))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist E))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist H))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist C))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist P))
            (locatedUniformCauchyPrincipleDecodeBHist
              (locatedUniformCauchyPrincipleEncodeBHist N))) =
          some (LocatedUniformCauchyPrincipleUp.mk D S R L B E H C P N)
      rw [locatedUniformCauchyPrinciple_decode_encode_bhist D,
        locatedUniformCauchyPrinciple_decode_encode_bhist S,
        locatedUniformCauchyPrinciple_decode_encode_bhist R,
        locatedUniformCauchyPrinciple_decode_encode_bhist L,
        locatedUniformCauchyPrinciple_decode_encode_bhist B,
        locatedUniformCauchyPrinciple_decode_encode_bhist E,
        locatedUniformCauchyPrinciple_decode_encode_bhist H,
        locatedUniformCauchyPrinciple_decode_encode_bhist C,
        locatedUniformCauchyPrinciple_decode_encode_bhist P,
        locatedUniformCauchyPrinciple_decode_encode_bhist N]

private theorem locatedUniformCauchyPrincipleToEventFlow_injective
    {x y : LocatedUniformCauchyPrincipleUp} :
    locatedUniformCauchyPrincipleToEventFlow x =
      locatedUniformCauchyPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUniformCauchyPrincipleFromEventFlow
          (locatedUniformCauchyPrincipleToEventFlow x) =
        locatedUniformCauchyPrincipleFromEventFlow
          (locatedUniformCauchyPrincipleToEventFlow y) :=
    congrArg locatedUniformCauchyPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedUniformCauchyPrinciple_round_trip x).symm
      (Eq.trans hread (locatedUniformCauchyPrinciple_round_trip y)))

instance locatedUniformCauchyPrincipleBHistCarrier :
    BHistCarrier LocatedUniformCauchyPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUniformCauchyPrincipleToEventFlow
  fromEventFlow := locatedUniformCauchyPrincipleFromEventFlow

instance locatedUniformCauchyPrincipleChapterTasteGate :
    ChapterTasteGate LocatedUniformCauchyPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedUniformCauchyPrincipleFromEventFlow
        (locatedUniformCauchyPrincipleToEventFlow x) = some x
    exact locatedUniformCauchyPrinciple_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedUniformCauchyPrincipleToEventFlow_injective heq)

instance locatedUniformCauchyPrincipleNontrivial :
    Nontrivial LocatedUniformCauchyPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedUniformCauchyPrincipleUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedUniformCauchyPrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedUniformCauchyPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedUniformCauchyPrincipleChapterTasteGate

theorem LocatedUniformCauchyPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedUniformCauchyPrincipleDecodeBHist
        (locatedUniformCauchyPrincipleEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedUniformCauchyPrincipleUp) ∧
        Nonempty (ChapterTasteGate LocatedUniformCauchyPrincipleUp) ∧
          locatedUniformCauchyPrincipleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedUniformCauchyPrinciple_decode_encode_bhist,
      ⟨locatedUniformCauchyPrincipleBHistCarrier⟩,
      ⟨locatedUniformCauchyPrincipleChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedUniformCauchyPrincipleUp
