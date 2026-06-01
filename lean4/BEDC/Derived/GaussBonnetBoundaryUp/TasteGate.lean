import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaussBonnetBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GaussBonnetBoundaryUp : Type where
  | mk :
      (surface metric curvature boundary form deRham euler transport replay provenance
        namecert : BHist) →
        GaussBonnetBoundaryUp
  deriving DecidableEq

def gaussBonnetBoundaryEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gaussBonnetBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gaussBonnetBoundaryEncodeBHist h

def gaussBonnetBoundaryDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gaussBonnetBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gaussBonnetBoundaryDecodeBHist tail)

private theorem gaussBonnetBoundaryDecode_encode_bhist :
    ∀ h : BHist, gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def gaussBonnetBoundaryToEventFlow : GaussBonnetBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GaussBonnetBoundaryUp.mk surface metric curvature boundary form deRham euler transport
      replay provenance namecert =>
      [[BMark.b0],
        gaussBonnetBoundaryEncodeBHist surface,
        [BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist metric,
        [BMark.b1, BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist curvature,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist form,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist deRham,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist euler,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        gaussBonnetBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaussBonnetBoundaryEncodeBHist namecert]

def gaussBonnetBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => gaussBonnetBoundaryEventAt index rest

def gaussBonnetBoundaryFromEventFlow : EventFlow → Option GaussBonnetBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (GaussBonnetBoundaryUp.mk
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 1 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 3 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 5 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 7 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 9 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 11 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 13 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 15 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 17 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 19 flow))
          (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEventAt 21 flow)))

private theorem gaussBonnetBoundary_round_trip :
    ∀ x : GaussBonnetBoundaryUp,
      gaussBonnetBoundaryFromEventFlow (gaussBonnetBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk surface metric curvature boundary form deRham euler transport replay provenance
      namecert =>
      change
        some
          (GaussBonnetBoundaryUp.mk
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist surface))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist metric))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist curvature))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist boundary))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist form))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist deRham))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist euler))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist transport))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist replay))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist provenance))
            (gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist namecert))) =
          some
            (GaussBonnetBoundaryUp.mk surface metric curvature boundary form deRham euler
              transport replay provenance namecert)
      rw [gaussBonnetBoundaryDecode_encode_bhist surface,
        gaussBonnetBoundaryDecode_encode_bhist metric,
        gaussBonnetBoundaryDecode_encode_bhist curvature,
        gaussBonnetBoundaryDecode_encode_bhist boundary,
        gaussBonnetBoundaryDecode_encode_bhist form,
        gaussBonnetBoundaryDecode_encode_bhist deRham,
        gaussBonnetBoundaryDecode_encode_bhist euler,
        gaussBonnetBoundaryDecode_encode_bhist transport,
        gaussBonnetBoundaryDecode_encode_bhist replay,
        gaussBonnetBoundaryDecode_encode_bhist provenance,
        gaussBonnetBoundaryDecode_encode_bhist namecert]

private theorem gaussBonnetBoundaryToEventFlow_injective (x y : GaussBonnetBoundaryUp) :
    gaussBonnetBoundaryToEventFlow x = gaussBonnetBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gaussBonnetBoundaryFromEventFlow (gaussBonnetBoundaryToEventFlow x) =
        gaussBonnetBoundaryFromEventFlow (gaussBonnetBoundaryToEventFlow y) :=
    congrArg gaussBonnetBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (gaussBonnetBoundary_round_trip x).symm
      (Eq.trans hread (gaussBonnetBoundary_round_trip y)))

instance gaussBonnetBoundaryBHistCarrier : BHistCarrier GaussBonnetBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gaussBonnetBoundaryToEventFlow
  fromEventFlow := gaussBonnetBoundaryFromEventFlow

instance gaussBonnetBoundaryChapterTasteGate : ChapterTasteGate GaussBonnetBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gaussBonnetBoundaryFromEventFlow (gaussBonnetBoundaryToEventFlow x) = some x
    exact gaussBonnetBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gaussBonnetBoundaryToEventFlow_injective x y heq)

def taste_gate : ChapterTasteGate GaussBonnetBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gaussBonnetBoundaryChapterTasteGate

theorem GaussBonnetBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, gaussBonnetBoundaryDecodeBHist (gaussBonnetBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier GaussBonnetBoundaryUp) ∧
        Nonempty (ChapterTasteGate GaussBonnetBoundaryUp) ∧
          gaussBonnetBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨gaussBonnetBoundaryDecode_encode_bhist,
      ⟨gaussBonnetBoundaryBHistCarrier⟩,
      ⟨gaussBonnetBoundaryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.GaussBonnetBoundaryUp.TasteGate
