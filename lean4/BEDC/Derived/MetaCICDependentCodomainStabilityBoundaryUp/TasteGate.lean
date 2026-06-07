import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDependentCodomainStabilityBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDependentCodomainStabilityBoundaryUp : Type where
  | mk (A D R I V Q L H C P N : BHist) : MetaCICDependentCodomainStabilityBoundaryUp
  deriving DecidableEq

def metacicDependentCodomainStabilityBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicDependentCodomainStabilityBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicDependentCodomainStabilityBoundaryEncodeBHist h

def metacicDependentCodomainStabilityBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicDependentCodomainStabilityBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicDependentCodomainStabilityBoundaryDecodeBHist tail)

private theorem metacicDependentCodomainStabilityBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      metacicDependentCodomainStabilityBoundaryDecodeBHist
        (metacicDependentCodomainStabilityBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicDependentCodomainStabilityBoundaryFields :
    MetaCICDependentCodomainStabilityBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDependentCodomainStabilityBoundaryUp.mk A D R I V Q L H C P N =>
      [A, D, R, I, V, Q, L, H, C, P, N]

def metacicDependentCodomainStabilityBoundaryToEventFlow :
    MetaCICDependentCodomainStabilityBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metacicDependentCodomainStabilityBoundaryFields x).map
      metacicDependentCodomainStabilityBoundaryEncodeBHist

def metacicDependentCodomainStabilityBoundaryFromEventFlow :
    EventFlow → Option MetaCICDependentCodomainStabilityBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | A :: D :: R :: I :: V :: Q :: L :: H :: C :: P :: N :: [] =>
      some
        (MetaCICDependentCodomainStabilityBoundaryUp.mk
          (metacicDependentCodomainStabilityBoundaryDecodeBHist A)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist D)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist R)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist I)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist V)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist Q)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist L)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist H)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist C)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist P)
          (metacicDependentCodomainStabilityBoundaryDecodeBHist N))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l ::
      _rest => none

private theorem metacicDependentCodomainStabilityBoundary_round_trip :
    ∀ x : MetaCICDependentCodomainStabilityBoundaryUp,
      metacicDependentCodomainStabilityBoundaryFromEventFlow
        (metacicDependentCodomainStabilityBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D R I V Q L H C P N =>
      change
        some
          (MetaCICDependentCodomainStabilityBoundaryUp.mk
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist A))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist D))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist R))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist I))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist V))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist Q))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist L))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist H))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist C))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist P))
            (metacicDependentCodomainStabilityBoundaryDecodeBHist
              (metacicDependentCodomainStabilityBoundaryEncodeBHist N))) =
          some (MetaCICDependentCodomainStabilityBoundaryUp.mk A D R I V Q L H C P N)
      rw [metacicDependentCodomainStabilityBoundaryDecode_encode_bhist A,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist D,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist R,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist I,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist V,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist Q,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist L,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist H,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist C,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist P,
        metacicDependentCodomainStabilityBoundaryDecode_encode_bhist N]

private theorem metacicDependentCodomainStabilityBoundaryToEventFlow_injective
    {x y : MetaCICDependentCodomainStabilityBoundaryUp} :
    metacicDependentCodomainStabilityBoundaryToEventFlow x =
      metacicDependentCodomainStabilityBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicDependentCodomainStabilityBoundaryFromEventFlow
          (metacicDependentCodomainStabilityBoundaryToEventFlow x) =
        metacicDependentCodomainStabilityBoundaryFromEventFlow
          (metacicDependentCodomainStabilityBoundaryToEventFlow y) :=
    congrArg metacicDependentCodomainStabilityBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicDependentCodomainStabilityBoundary_round_trip x).symm
      (Eq.trans hread (metacicDependentCodomainStabilityBoundary_round_trip y)))

private theorem metacicDependentCodomainStabilityBoundary_fields_faithful :
    ∀ x y : MetaCICDependentCodomainStabilityBoundaryUp,
      metacicDependentCodomainStabilityBoundaryFields x =
        metacicDependentCodomainStabilityBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A D R I V Q L H C P N =>
      cases y with
      | mk A' D' R' I' V' Q' L' H' C' P' N' =>
          cases hfields
          rfl

instance metacicDependentCodomainStabilityBoundaryBHistCarrier :
    BHistCarrier MetaCICDependentCodomainStabilityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicDependentCodomainStabilityBoundaryToEventFlow
  fromEventFlow := metacicDependentCodomainStabilityBoundaryFromEventFlow

instance metacicDependentCodomainStabilityBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICDependentCodomainStabilityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicDependentCodomainStabilityBoundaryFromEventFlow
        (metacicDependentCodomainStabilityBoundaryToEventFlow x) = some x
    exact metacicDependentCodomainStabilityBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicDependentCodomainStabilityBoundaryToEventFlow_injective heq)

instance metacicDependentCodomainStabilityBoundaryFieldFaithful :
    FieldFaithful MetaCICDependentCodomainStabilityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicDependentCodomainStabilityBoundaryFields
  field_faithful := metacicDependentCodomainStabilityBoundary_fields_faithful

instance metacicDependentCodomainStabilityBoundaryNontrivial :
    Nontrivial MetaCICDependentCodomainStabilityBoundaryUp where
  witness_pair :=
    ⟨MetaCICDependentCodomainStabilityBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICDependentCodomainStabilityBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICDependentCodomainStabilityBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicDependentCodomainStabilityBoundaryChapterTasteGate

theorem MetaCICDependentCodomainStabilityBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metacicDependentCodomainStabilityBoundaryDecodeBHist
          (metacicDependentCodomainStabilityBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetaCICDependentCodomainStabilityBoundaryUp) ∧
        Nonempty (ChapterTasteGate MetaCICDependentCodomainStabilityBoundaryUp) ∧
          metacicDependentCodomainStabilityBoundaryEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨metacicDependentCodomainStabilityBoundaryDecode_encode_bhist,
      ⟨metacicDependentCodomainStabilityBoundaryBHistCarrier⟩,
      ⟨metacicDependentCodomainStabilityBoundaryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetaCICDependentCodomainStabilityBoundaryUp.TasteGate
