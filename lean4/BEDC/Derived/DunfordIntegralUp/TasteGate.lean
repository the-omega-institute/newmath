import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DunfordIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DunfordIntegralUp : Type where
  | mk (M I X V L W A B S R H C P N : BHist) : DunfordIntegralUp
  deriving DecidableEq

def dunfordIntegralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dunfordIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dunfordIntegralEncodeBHist h

def dunfordIntegralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dunfordIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dunfordIntegralDecodeBHist tail)

private theorem dunfordIntegralDecode_encode_bhist :
    ∀ h : BHist, dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dunfordIntegralFields : DunfordIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DunfordIntegralUp.mk M I X V L W A B S R H C P N =>
      [M, I, X, V, L, W, A, B, S, R, H, C, P, N]

def dunfordIntegralToEventFlow : DunfordIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DunfordIntegralUp.mk M I X V L W A B S R H C P N =>
      [dunfordIntegralEncodeBHist M, dunfordIntegralEncodeBHist I,
        dunfordIntegralEncodeBHist X, dunfordIntegralEncodeBHist V,
        dunfordIntegralEncodeBHist L, dunfordIntegralEncodeBHist W,
        dunfordIntegralEncodeBHist A, dunfordIntegralEncodeBHist B,
        dunfordIntegralEncodeBHist S, dunfordIntegralEncodeBHist R,
        dunfordIntegralEncodeBHist H, dunfordIntegralEncodeBHist C,
        dunfordIntegralEncodeBHist P, dunfordIntegralEncodeBHist N]

def dunfordIntegralFromEventFlow : EventFlow → Option DunfordIntegralUp
  -- BEDC touchpoint anchor: BHist BMark
  | [M, I, X, V, L, W, A, B, S, R, H, C, P, N] =>
      some
        (DunfordIntegralUp.mk
          (dunfordIntegralDecodeBHist M)
          (dunfordIntegralDecodeBHist I)
          (dunfordIntegralDecodeBHist X)
          (dunfordIntegralDecodeBHist V)
          (dunfordIntegralDecodeBHist L)
          (dunfordIntegralDecodeBHist W)
          (dunfordIntegralDecodeBHist A)
          (dunfordIntegralDecodeBHist B)
          (dunfordIntegralDecodeBHist S)
          (dunfordIntegralDecodeBHist R)
          (dunfordIntegralDecodeBHist H)
          (dunfordIntegralDecodeBHist C)
          (dunfordIntegralDecodeBHist P)
          (dunfordIntegralDecodeBHist N))
  | _ => none

private theorem dunfordIntegral_round_trip :
    ∀ x : DunfordIntegralUp,
      dunfordIntegralFromEventFlow (dunfordIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M I X V L W A B S R H C P N =>
      change
        some
          (DunfordIntegralUp.mk
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist M))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist I))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist X))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist V))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist L))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist W))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist A))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist B))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist S))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist R))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist H))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist C))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist P))
            (dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist N))) =
          some (DunfordIntegralUp.mk M I X V L W A B S R H C P N)
      rw [dunfordIntegralDecode_encode_bhist M, dunfordIntegralDecode_encode_bhist I,
        dunfordIntegralDecode_encode_bhist X, dunfordIntegralDecode_encode_bhist V,
        dunfordIntegralDecode_encode_bhist L, dunfordIntegralDecode_encode_bhist W,
        dunfordIntegralDecode_encode_bhist A, dunfordIntegralDecode_encode_bhist B,
        dunfordIntegralDecode_encode_bhist S, dunfordIntegralDecode_encode_bhist R,
        dunfordIntegralDecode_encode_bhist H, dunfordIntegralDecode_encode_bhist C,
        dunfordIntegralDecode_encode_bhist P, dunfordIntegralDecode_encode_bhist N]

private theorem dunfordIntegralToEventFlow_injective {x y : DunfordIntegralUp} :
    dunfordIntegralToEventFlow x = dunfordIntegralToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dunfordIntegralFromEventFlow (dunfordIntegralToEventFlow x) =
        dunfordIntegralFromEventFlow (dunfordIntegralToEventFlow y) :=
    congrArg dunfordIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dunfordIntegral_round_trip x).symm
      (Eq.trans hread (dunfordIntegral_round_trip y)))

instance dunfordIntegralBHistCarrier : BHistCarrier DunfordIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dunfordIntegralToEventFlow
  fromEventFlow := dunfordIntegralFromEventFlow

instance dunfordIntegralChapterTasteGate : ChapterTasteGate DunfordIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dunfordIntegralFromEventFlow (dunfordIntegralToEventFlow x) = some x
    exact dunfordIntegral_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dunfordIntegralToEventFlow_injective heq)

theorem DunfordIntegralTasteGate_single_carrier_alignment :
    Nonempty DunfordIntegralUp ∧
      dunfordIntegralEncodeBHist BHist.Empty = ([] : RawEvent) ∧
        dunfordIntegralEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
          (∀ h : BHist, dunfordIntegralDecodeBHist (dunfordIntegralEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact
      ⟨DunfordIntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty⟩
  · constructor
    · rfl
    · constructor
      · rfl
      · exact dunfordIntegralDecode_encode_bhist

end BEDC.Derived.DunfordIntegralUp
