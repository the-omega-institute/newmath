import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PackageMapBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PackageMapBoundaryUp : Type where
  | mk (T G R S X A H C P N : BHist) : PackageMapBoundaryUp
  deriving DecidableEq

def packageMapBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: packageMapBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: packageMapBoundaryEncodeBHist h

def packageMapBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (packageMapBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (packageMapBoundaryDecodeBHist tail)

private theorem packageMapBoundaryDecode_encode_bhist :
    ∀ h : BHist, packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def packageMapBoundaryFields : PackageMapBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PackageMapBoundaryUp.mk T G R S X A H C P N => [T, G, R, S, X, A, H, C, P, N]

def packageMapBoundaryToEventFlow : PackageMapBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PackageMapBoundaryUp.mk T G R S X A H C P N =>
      [[BMark.b0],
        packageMapBoundaryEncodeBHist T,
        [BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        packageMapBoundaryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        packageMapBoundaryEncodeBHist N]

private def packageMapBoundaryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => packageMapBoundaryRawAt n rest

private def packageMapBoundaryLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => packageMapBoundaryLengthEq n rest

def packageMapBoundaryFromEventFlow : EventFlow → Option PackageMapBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match packageMapBoundaryLengthEq 20 flow with
      | true =>
          some
            (PackageMapBoundaryUp.mk
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 1 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 3 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 5 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 7 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 9 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 11 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 13 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 15 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 17 flow))
              (packageMapBoundaryDecodeBHist (packageMapBoundaryRawAt 19 flow)))
      | false => none

private theorem packageMapBoundary_round_trip :
    ∀ x : PackageMapBoundaryUp,
      packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T G R S X A H C P N =>
      change
        some
          (PackageMapBoundaryUp.mk
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist T))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist G))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist R))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist S))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist X))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist A))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist H))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist C))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist P))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist N))) =
          some (PackageMapBoundaryUp.mk T G R S X A H C P N)
      rw [packageMapBoundaryDecode_encode_bhist T,
        packageMapBoundaryDecode_encode_bhist G,
        packageMapBoundaryDecode_encode_bhist R,
        packageMapBoundaryDecode_encode_bhist S,
        packageMapBoundaryDecode_encode_bhist X,
        packageMapBoundaryDecode_encode_bhist A,
        packageMapBoundaryDecode_encode_bhist H,
        packageMapBoundaryDecode_encode_bhist C,
        packageMapBoundaryDecode_encode_bhist P,
        packageMapBoundaryDecode_encode_bhist N]

private theorem packageMapBoundaryToEventFlow_injective
    {x y : PackageMapBoundaryUp} :
    packageMapBoundaryToEventFlow x = packageMapBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) =
        packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow y) :=
    congrArg packageMapBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (packageMapBoundary_round_trip x).symm
      (Eq.trans hread (packageMapBoundary_round_trip y)))

private theorem packageMapBoundary_field_faithful :
    ∀ x y : PackageMapBoundaryUp,
      packageMapBoundaryFields x = packageMapBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 G1 R1 S1 X1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 G2 R2 S2 X2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance packageMapBoundaryBHistCarrier : BHistCarrier PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := packageMapBoundaryToEventFlow
  fromEventFlow := packageMapBoundaryFromEventFlow

instance packageMapBoundaryChapterTasteGate :
    ChapterTasteGate PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x
    exact packageMapBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (packageMapBoundaryToEventFlow_injective heq)

instance packageMapBoundaryFieldFaithful : FieldFaithful PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := packageMapBoundaryFields
  field_faithful := packageMapBoundary_field_faithful

instance packageMapBoundaryNontrivial : Nontrivial PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PackageMapBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PackageMapBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PackageMapBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  packageMapBoundaryChapterTasteGate

theorem PackageMapBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist h) = h) ∧
      (∀ x : PackageMapBoundaryUp,
        packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x) ∧
        (∀ x y : PackageMapBoundaryUp,
          packageMapBoundaryToEventFlow x = packageMapBoundaryToEventFlow y → x = y) ∧
          packageMapBoundaryFields
              (PackageMapBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨packageMapBoundaryDecode_encode_bhist,
      packageMapBoundary_round_trip,
      (fun _ _ heq => packageMapBoundaryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PackageMapBoundaryUp
