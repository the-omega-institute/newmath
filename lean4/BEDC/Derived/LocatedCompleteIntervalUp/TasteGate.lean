import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompleteIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompleteIntervalUp : Type where
  | mk (B L N Q D S R E K H C P M : BHist) : LocatedCompleteIntervalUp
  deriving DecidableEq

def locatedCompleteIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompleteIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompleteIntervalEncodeBHist h

def locatedCompleteIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompleteIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompleteIntervalDecodeBHist tail)

private theorem locatedCompleteIntervalDecodeEncode :
    ∀ h : BHist, locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompleteIntervalToEventFlow : LocatedCompleteIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompleteIntervalUp.mk B L N Q D S R E K H C P M =>
      [[BMark.b0],
        locatedCompleteIntervalEncodeBHist B,
        [BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedCompleteIntervalEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompleteIntervalEncodeBHist M]

private def locatedCompleteIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompleteIntervalEventAtDefault index rest

def locatedCompleteIntervalFromEventFlow (ef : EventFlow) : Option LocatedCompleteIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompleteIntervalUp.mk
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 1 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 3 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 5 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 7 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 9 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 11 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 13 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 15 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 17 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 19 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 21 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 23 ef))
      (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEventAtDefault 25 ef)))

private theorem locatedCompleteIntervalRoundTrip :
    ∀ x : LocatedCompleteIntervalUp,
      locatedCompleteIntervalFromEventFlow (locatedCompleteIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L N Q D S R E K H C P M =>
      change
        some
          (LocatedCompleteIntervalUp.mk
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist B))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist L))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist N))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist Q))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist D))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist S))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist R))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist E))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist K))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist H))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist C))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist P))
            (locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist M))) =
          some (LocatedCompleteIntervalUp.mk B L N Q D S R E K H C P M)
      rw [locatedCompleteIntervalDecodeEncode B, locatedCompleteIntervalDecodeEncode L,
        locatedCompleteIntervalDecodeEncode N, locatedCompleteIntervalDecodeEncode Q,
        locatedCompleteIntervalDecodeEncode D, locatedCompleteIntervalDecodeEncode S,
        locatedCompleteIntervalDecodeEncode R, locatedCompleteIntervalDecodeEncode E,
        locatedCompleteIntervalDecodeEncode K, locatedCompleteIntervalDecodeEncode H,
        locatedCompleteIntervalDecodeEncode C, locatedCompleteIntervalDecodeEncode P,
        locatedCompleteIntervalDecodeEncode M]

private theorem locatedCompleteIntervalToEventFlow_injective {x y : LocatedCompleteIntervalUp} :
    locatedCompleteIntervalToEventFlow x = locatedCompleteIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompleteIntervalFromEventFlow (locatedCompleteIntervalToEventFlow x) =
        locatedCompleteIntervalFromEventFlow (locatedCompleteIntervalToEventFlow y) :=
    congrArg locatedCompleteIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCompleteIntervalRoundTrip x).symm
      (Eq.trans hread (locatedCompleteIntervalRoundTrip y)))

def locatedCompleteIntervalFields : LocatedCompleteIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompleteIntervalUp.mk B L N Q D S R E K H C P M =>
      [B, L, N, Q, D, S, R, E, K, H, C, P, M]

instance locatedCompleteIntervalBHistCarrier : BHistCarrier LocatedCompleteIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompleteIntervalToEventFlow
  fromEventFlow := locatedCompleteIntervalFromEventFlow

instance locatedCompleteIntervalChapterTasteGate :
    ChapterTasteGate LocatedCompleteIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompleteIntervalFromEventFlow (locatedCompleteIntervalToEventFlow x) = some x
    exact locatedCompleteIntervalRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCompleteIntervalToEventFlow_injective heq)

instance locatedCompleteIntervalFieldFaithful : FieldFaithful LocatedCompleteIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCompleteIntervalFields
  field_faithful := by
    intro x y h
    cases x with
    | mk B₁ L₁ N₁ Q₁ D₁ S₁ R₁ E₁ K₁ H₁ C₁ P₁ M₁ =>
      cases y with
      | mk B₂ L₂ N₂ Q₂ D₂ S₂ R₂ E₂ K₂ H₂ C₂ P₂ M₂ =>
        change [B₁, L₁, N₁, Q₁, D₁, S₁, R₁, E₁, K₁, H₁, C₁, P₁, M₁] =
          [B₂, L₂, N₂, Q₂, D₂, S₂, R₂, E₂, K₂, H₂, C₂, P₂, M₂] at h
        cases h
        rfl

instance locatedCompleteIntervalNontrivial : Nontrivial LocatedCompleteIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCompleteIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedCompleteIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedCompleteIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCompleteIntervalDecodeBHist (locatedCompleteIntervalEncodeBHist h) = h) ∧
      (∀ x : LocatedCompleteIntervalUp,
        locatedCompleteIntervalFromEventFlow (locatedCompleteIntervalToEventFlow x) = some x) ∧
        (∀ x y : LocatedCompleteIntervalUp,
          locatedCompleteIntervalToEventFlow x = locatedCompleteIntervalToEventFlow y → x = y) ∧
          locatedCompleteIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨locatedCompleteIntervalDecodeEncode,
      locatedCompleteIntervalRoundTrip,
      fun _ _ heq => locatedCompleteIntervalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedCompleteIntervalUp
