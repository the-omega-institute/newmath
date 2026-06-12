import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CoverageRankAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CoverageRankAlgebraUp : Type where
  | mk (B R T L F Q H C P N : BHist) : CoverageRankAlgebraUp
  deriving DecidableEq

def coverageRankAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: coverageRankAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: coverageRankAlgebraEncodeBHist h

def coverageRankAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (coverageRankAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (coverageRankAlgebraDecodeBHist tail)

private theorem coverageRankAlgebra_decode_encode_bhist :
    ∀ h : BHist,
      coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def coverageRankAlgebraFields : CoverageRankAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CoverageRankAlgebraUp.mk B R T L F Q H C P N => [B, R, T, L, F, Q, H, C, P, N]

def coverageRankAlgebraToEventFlow : CoverageRankAlgebraUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (coverageRankAlgebraFields x).map coverageRankAlgebraEncodeBHist

private def coverageRankAlgebraEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => coverageRankAlgebraEventAtDefault index rest

def coverageRankAlgebraFromEventFlow (ef : EventFlow) : Option CoverageRankAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CoverageRankAlgebraUp.mk
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 0 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 1 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 2 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 3 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 4 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 5 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 6 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 7 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 8 ef))
      (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEventAtDefault 9 ef)))

private theorem coverageRankAlgebra_round_trip (x : CoverageRankAlgebraUp) :
    coverageRankAlgebraFromEventFlow (coverageRankAlgebraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B R T L F Q H C P N =>
      change
        some
          (CoverageRankAlgebraUp.mk
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist B))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist R))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist T))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist L))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist F))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist Q))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist H))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist C))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist P))
            (coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist N))) =
          some (CoverageRankAlgebraUp.mk B R T L F Q H C P N)
      rw [coverageRankAlgebra_decode_encode_bhist B, coverageRankAlgebra_decode_encode_bhist R,
        coverageRankAlgebra_decode_encode_bhist T, coverageRankAlgebra_decode_encode_bhist L,
        coverageRankAlgebra_decode_encode_bhist F, coverageRankAlgebra_decode_encode_bhist Q,
        coverageRankAlgebra_decode_encode_bhist H, coverageRankAlgebra_decode_encode_bhist C,
        coverageRankAlgebra_decode_encode_bhist P, coverageRankAlgebra_decode_encode_bhist N]

private theorem coverageRankAlgebraToEventFlow_injective {x y : CoverageRankAlgebraUp} :
    coverageRankAlgebraToEventFlow x = coverageRankAlgebraToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      coverageRankAlgebraFromEventFlow (coverageRankAlgebraToEventFlow x) =
        coverageRankAlgebraFromEventFlow (coverageRankAlgebraToEventFlow y) :=
    congrArg coverageRankAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (coverageRankAlgebra_round_trip x).symm
      (Eq.trans hread (coverageRankAlgebra_round_trip y)))

private theorem coverageRankAlgebra_fields_faithful :
    ∀ x y : CoverageRankAlgebraUp, coverageRankAlgebraFields x = coverageRankAlgebraFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk B₁ R₁ T₁ L₁ F₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ R₂ T₂ L₂ F₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection h with hB t1
          injection t1 with hR t2
          injection t2 with hT t3
          injection t3 with hL t4
          injection t4 with hF t5
          injection t5 with hQ t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hB
          cases hR
          cases hT
          cases hL
          cases hF
          cases hQ
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance coverageRankAlgebraBHistCarrier : BHistCarrier CoverageRankAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := coverageRankAlgebraToEventFlow
  fromEventFlow := coverageRankAlgebraFromEventFlow

instance coverageRankAlgebraChapterTasteGate : ChapterTasteGate CoverageRankAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change coverageRankAlgebraFromEventFlow (coverageRankAlgebraToEventFlow x) = some x
    exact coverageRankAlgebra_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (coverageRankAlgebraToEventFlow_injective heq)

instance coverageRankAlgebraFieldFaithful : FieldFaithful CoverageRankAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := coverageRankAlgebraFields
  field_faithful := coverageRankAlgebra_fields_faithful

instance coverageRankAlgebraNontrivial : Nontrivial CoverageRankAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CoverageRankAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CoverageRankAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CoverageRankAlgebra_taste_gate : ChapterTasteGate CoverageRankAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  coverageRankAlgebraChapterTasteGate

theorem CoverageRankAlgebra_single_carrier_alignment :
    (∀ h : BHist, coverageRankAlgebraDecodeBHist (coverageRankAlgebraEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate CoverageRankAlgebraUp) ∧
        Nonempty (FieldFaithful CoverageRankAlgebraUp) ∧ Nonempty (Nontrivial CoverageRankAlgebraUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨coverageRankAlgebra_decode_encode_bhist, ⟨coverageRankAlgebraChapterTasteGate⟩,
      ⟨coverageRankAlgebraFieldFaithful⟩, ⟨coverageRankAlgebraNontrivial⟩⟩

end BEDC.Derived.CoverageRankAlgebraUp
