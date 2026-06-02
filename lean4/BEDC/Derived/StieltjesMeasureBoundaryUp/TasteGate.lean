import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StieltjesMeasureBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StieltjesMeasureBoundaryUp : Type where
  | mk (B Pi J R E H C P N : BHist) : StieltjesMeasureBoundaryUp
  deriving DecidableEq

def stieltjesMeasureBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stieltjesMeasureBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stieltjesMeasureBoundaryEncodeBHist h

def stieltjesMeasureBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stieltjesMeasureBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stieltjesMeasureBoundaryDecodeBHist tail)

private theorem stieltjesMeasureBoundary_decode_encode :
    ∀ h : BHist, stieltjesMeasureBoundaryDecodeBHist
      (stieltjesMeasureBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stieltjesMeasureBoundaryFields : StieltjesMeasureBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StieltjesMeasureBoundaryUp.mk B Pi J R E H C P N => [B, Pi, J, R, E, H, C, P, N]

def stieltjesMeasureBoundaryToEventFlow : StieltjesMeasureBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (stieltjesMeasureBoundaryFields x).map stieltjesMeasureBoundaryEncodeBHist

private def stieltjesMeasureBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => stieltjesMeasureBoundaryEventAt index rest

def stieltjesMeasureBoundaryFromEventFlow (ef : EventFlow) : Option StieltjesMeasureBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StieltjesMeasureBoundaryUp.mk
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 0 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 1 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 2 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 3 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 4 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 5 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 6 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 7 ef))
      (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEventAt 8 ef)))

private theorem stieltjesMeasureBoundary_round_trip :
    ∀ x : StieltjesMeasureBoundaryUp,
      stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Pi J R E H C P N =>
      change
        some
          (StieltjesMeasureBoundaryUp.mk
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist B))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist Pi))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist J))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist R))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist E))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist H))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist C))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist P))
            (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist N))) =
          some (StieltjesMeasureBoundaryUp.mk B Pi J R E H C P N)
      rw [stieltjesMeasureBoundary_decode_encode B,
        stieltjesMeasureBoundary_decode_encode Pi,
        stieltjesMeasureBoundary_decode_encode J,
        stieltjesMeasureBoundary_decode_encode R,
        stieltjesMeasureBoundary_decode_encode E,
        stieltjesMeasureBoundary_decode_encode H,
        stieltjesMeasureBoundary_decode_encode C,
        stieltjesMeasureBoundary_decode_encode P,
        stieltjesMeasureBoundary_decode_encode N]

private theorem stieltjesMeasureBoundary_toEventFlow_injective
    {x y : StieltjesMeasureBoundaryUp} :
    stieltjesMeasureBoundaryToEventFlow x = stieltjesMeasureBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow x) =
        stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow y) :=
    congrArg stieltjesMeasureBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stieltjesMeasureBoundary_round_trip x).symm
      (Eq.trans hread (stieltjesMeasureBoundary_round_trip y)))

private theorem stieltjesMeasureBoundary_fields_faithful :
    ∀ x y : StieltjesMeasureBoundaryUp,
      stieltjesMeasureBoundaryFields x = stieltjesMeasureBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ Pi₁ J₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ Pi₂ J₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hB t0
          injection t0 with hPi t1
          injection t1 with hJ t2
          injection t2 with hR t3
          injection t3 with hE t4
          injection t4 with hH t5
          injection t5 with hC t6
          injection t6 with hP t7
          injection t7 with hN _
          subst hB
          subst hPi
          subst hJ
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance stieltjesMeasureBoundaryBHistCarrier : BHistCarrier StieltjesMeasureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stieltjesMeasureBoundaryToEventFlow
  fromEventFlow := stieltjesMeasureBoundaryFromEventFlow

instance stieltjesMeasureBoundaryChapterTasteGate :
    ChapterTasteGate StieltjesMeasureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stieltjesMeasureBoundaryFromEventFlow
      (stieltjesMeasureBoundaryToEventFlow x) = some x
    exact stieltjesMeasureBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stieltjesMeasureBoundary_toEventFlow_injective heq)

instance stieltjesMeasureBoundaryFieldFaithful : FieldFaithful StieltjesMeasureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stieltjesMeasureBoundaryFields
  field_faithful := stieltjesMeasureBoundary_fields_faithful

instance stieltjesMeasureBoundaryNontrivial :
    BEDC.Meta.TasteGate.Nontrivial StieltjesMeasureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StieltjesMeasureBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StieltjesMeasureBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem StieltjesMeasureBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate StieltjesMeasureBoundaryUp) ∧
      Nonempty (FieldFaithful StieltjesMeasureBoundaryUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial StieltjesMeasureBoundaryUp) ∧
      (∀ h : BHist,
        stieltjesMeasureBoundaryDecodeBHist
          (stieltjesMeasureBoundaryEncodeBHist h) = h) ∧
      (∀ x : StieltjesMeasureBoundaryUp,
        stieltjesMeasureBoundaryFromEventFlow
          (stieltjesMeasureBoundaryToEventFlow x) = some x) ∧
      stieltjesMeasureBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨stieltjesMeasureBoundaryChapterTasteGate⟩,
      ⟨stieltjesMeasureBoundaryFieldFaithful⟩,
      ⟨stieltjesMeasureBoundaryNontrivial⟩,
      stieltjesMeasureBoundary_decode_encode,
      stieltjesMeasureBoundary_round_trip,
      rfl⟩

end BEDC.Derived.StieltjesMeasureBoundaryUp.TasteGate
