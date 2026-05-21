import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicTailBoundUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicTailBoundUp : Type where
  | mk (p mu epsilon L R E H C P N : BHist) : DyadicTailBoundUp
  deriving DecidableEq

def dyadicTailBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicTailBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicTailBoundEncodeBHist h

def dyadicTailBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicTailBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicTailBoundDecodeBHist tail)

private theorem dyadicTailBoundDecode_encode_bhist :
    ∀ h : BHist, dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicTailBoundToEventFlow : DyadicTailBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicTailBoundUp.mk p mu epsilon L R E H C P N =>
      [[BMark.b0],
        dyadicTailBoundEncodeBHist p,
        [BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist mu,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist epsilon,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicTailBoundEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        dyadicTailBoundEncodeBHist N]

def dyadicTailBoundFromEventFlow : EventFlow → Option DyadicTailBoundUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tagP :: p :: _tagMu :: mu :: _tagEpsilon :: epsilon :: _tagL :: L ::
      _tagR :: R :: _tagE :: E :: _tagH :: H :: _tagC :: C :: _tagPkg :: P ::
      _tagN :: N :: [] =>
      some
        (DyadicTailBoundUp.mk
          (dyadicTailBoundDecodeBHist p)
          (dyadicTailBoundDecodeBHist mu)
          (dyadicTailBoundDecodeBHist epsilon)
          (dyadicTailBoundDecodeBHist L)
          (dyadicTailBoundDecodeBHist R)
          (dyadicTailBoundDecodeBHist E)
          (dyadicTailBoundDecodeBHist H)
          (dyadicTailBoundDecodeBHist C)
          (dyadicTailBoundDecodeBHist P)
          (dyadicTailBoundDecodeBHist N))
  | _ => none

private theorem dyadicTailBound_round_trip :
    ∀ x : DyadicTailBoundUp,
      dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk p mu epsilon L R E H C P N =>
      change
        some
          (DyadicTailBoundUp.mk
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist p))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist mu))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist epsilon))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist L))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist R))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist E))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist H))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist C))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist P))
            (dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist N))) =
          some (DyadicTailBoundUp.mk p mu epsilon L R E H C P N)
      rw [dyadicTailBoundDecode_encode_bhist p, dyadicTailBoundDecode_encode_bhist mu,
        dyadicTailBoundDecode_encode_bhist epsilon, dyadicTailBoundDecode_encode_bhist L,
        dyadicTailBoundDecode_encode_bhist R, dyadicTailBoundDecode_encode_bhist E,
        dyadicTailBoundDecode_encode_bhist H, dyadicTailBoundDecode_encode_bhist C,
        dyadicTailBoundDecode_encode_bhist P, dyadicTailBoundDecode_encode_bhist N]

private theorem dyadicTailBoundToEventFlow_injective {x y : DyadicTailBoundUp} :
    dyadicTailBoundToEventFlow x = dyadicTailBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow x) =
        dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow y) :=
    congrArg dyadicTailBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicTailBound_round_trip x).symm
      (Eq.trans hread (dyadicTailBound_round_trip y)))

private def dyadicTailBoundFields : DyadicTailBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicTailBoundUp.mk p mu epsilon L R E H C P N => [p, mu, epsilon, L, R, E, H, C, P, N]

private theorem dyadicTailBound_fields_faithful :
    ∀ x y : DyadicTailBoundUp, dyadicTailBoundFields x = dyadicTailBoundFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk p1 mu1 epsilon1 L1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk p2 mu2 epsilon2 L2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicTailBoundBHistCarrier : BHistCarrier DyadicTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicTailBoundToEventFlow
  fromEventFlow := dyadicTailBoundFromEventFlow

instance dyadicTailBoundChapterTasteGate : ChapterTasteGate DyadicTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow x) = some x
    exact dyadicTailBound_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicTailBoundToEventFlow_injective heq)

instance dyadicTailBoundFieldFaithful : FieldFaithful DyadicTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicTailBoundFields
  field_faithful := dyadicTailBound_fields_faithful

instance dyadicTailBoundNontrivial : Nontrivial DyadicTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicTailBoundUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicTailBoundUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DyadicTailBoundTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicTailBoundUp) ∧
      Nonempty (FieldFaithful DyadicTailBoundUp) ∧
      Nonempty (Nontrivial DyadicTailBoundUp) ∧
      (∀ h : BHist, dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist h) = h) ∧
      (∀ x : DyadicTailBoundUp,
        dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow x) = some x) ∧
      (∀ x y : DyadicTailBoundUp,
        dyadicTailBoundToEventFlow x = dyadicTailBoundToEventFlow y → x = y) ∧
      dyadicTailBoundEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact
      ⟨{
        round_trip := by
          intro x
          change dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow x) = some x
          exact dyadicTailBound_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (dyadicTailBoundToEventFlow_injective heq)
      }⟩
  constructor
  · exact
      ⟨{
        fields := dyadicTailBoundFields
        field_faithful := dyadicTailBound_fields_faithful
      }⟩
  constructor
  · exact
      ⟨{
        witness_pair :=
          ⟨DyadicTailBoundUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            DyadicTailBoundUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            by
              intro h
              cases h⟩
      }⟩
  constructor
  · exact dyadicTailBoundDecode_encode_bhist
  constructor
  · exact dyadicTailBound_round_trip
  constructor
  · intro x y heq
    exact dyadicTailBoundToEventFlow_injective heq
  · rfl

end BEDC.Derived.DyadicTailBoundUp.TasteGate
