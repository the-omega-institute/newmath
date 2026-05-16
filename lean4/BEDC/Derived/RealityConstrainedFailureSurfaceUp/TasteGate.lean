import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedFailureSurfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedFailureSurfaceUp : Type where
  | mk (O D K U L H C P N : BHist) : RealityConstrainedFailureSurfaceUp
  deriving DecidableEq

def realityConstrainedFailureSurfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedFailureSurfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedFailureSurfaceEncodeBHist h

def realityConstrainedFailureSurfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedFailureSurfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedFailureSurfaceDecodeBHist tail)

private theorem realityConstrainedFailureSurfaceDecodeEncodeBHist :
    ∀ h : BHist,
      realityConstrainedFailureSurfaceDecodeBHist
        (realityConstrainedFailureSurfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedFailureSurfaceFields :
    RealityConstrainedFailureSurfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N =>
      [O, D, K, U, L, H, C, P, N]

def realityConstrainedFailureSurfaceToEventFlow :
    RealityConstrainedFailureSurfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (realityConstrainedFailureSurfaceFields x).map
        realityConstrainedFailureSurfaceEncodeBHist

def realityConstrainedFailureSurfaceFromEventFlow :
    EventFlow → Option RealityConstrainedFailureSurfaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | O :: D :: K :: U :: L :: H :: C :: P :: N :: [] =>
      some
        (RealityConstrainedFailureSurfaceUp.mk
          (realityConstrainedFailureSurfaceDecodeBHist O)
          (realityConstrainedFailureSurfaceDecodeBHist D)
          (realityConstrainedFailureSurfaceDecodeBHist K)
          (realityConstrainedFailureSurfaceDecodeBHist U)
          (realityConstrainedFailureSurfaceDecodeBHist L)
          (realityConstrainedFailureSurfaceDecodeBHist H)
          (realityConstrainedFailureSurfaceDecodeBHist C)
          (realityConstrainedFailureSurfaceDecodeBHist P)
          (realityConstrainedFailureSurfaceDecodeBHist N))
  | _ => none

private theorem realityConstrainedFailureSurface_round_trip :
    ∀ x : RealityConstrainedFailureSurfaceUp,
      realityConstrainedFailureSurfaceFromEventFlow
        (realityConstrainedFailureSurfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O D K U L H C P N =>
      change
        some
          (RealityConstrainedFailureSurfaceUp.mk
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist O))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist D))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist K))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist U))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist L))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist H))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist C))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist P))
            (realityConstrainedFailureSurfaceDecodeBHist
              (realityConstrainedFailureSurfaceEncodeBHist N))) =
          some (RealityConstrainedFailureSurfaceUp.mk O D K U L H C P N)
      rw [realityConstrainedFailureSurfaceDecodeEncodeBHist O,
        realityConstrainedFailureSurfaceDecodeEncodeBHist D,
        realityConstrainedFailureSurfaceDecodeEncodeBHist K,
        realityConstrainedFailureSurfaceDecodeEncodeBHist U,
        realityConstrainedFailureSurfaceDecodeEncodeBHist L,
        realityConstrainedFailureSurfaceDecodeEncodeBHist H,
        realityConstrainedFailureSurfaceDecodeEncodeBHist C,
        realityConstrainedFailureSurfaceDecodeEncodeBHist P,
        realityConstrainedFailureSurfaceDecodeEncodeBHist N]

private theorem realityConstrainedFailureSurfaceToEventFlow_injective
    {x y : RealityConstrainedFailureSurfaceUp} :
    realityConstrainedFailureSurfaceToEventFlow x =
      realityConstrainedFailureSurfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedFailureSurfaceFromEventFlow
          (realityConstrainedFailureSurfaceToEventFlow x) =
        realityConstrainedFailureSurfaceFromEventFlow
          (realityConstrainedFailureSurfaceToEventFlow y) :=
    congrArg realityConstrainedFailureSurfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedFailureSurface_round_trip x).symm
      (Eq.trans hread (realityConstrainedFailureSurface_round_trip y)))

private theorem realityConstrainedFailureSurface_fields_faithful :
    ∀ x y : RealityConstrainedFailureSurfaceUp,
      realityConstrainedFailureSurfaceFields x =
        realityConstrainedFailureSurfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ D₁ K₁ U₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ D₂ K₂ U₂ L₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hO t0
          injection t0 with hD t1
          injection t1 with hK t2
          injection t2 with hU t3
          injection t3 with hL t4
          injection t4 with hH t5
          injection t5 with hC t6
          injection t6 with hP t7
          injection t7 with hN _
          subst hO
          subst hD
          subst hK
          subst hU
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realityConstrainedFailureSurfaceBHistCarrier :
    BHistCarrier RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedFailureSurfaceToEventFlow
  fromEventFlow := realityConstrainedFailureSurfaceFromEventFlow

instance realityConstrainedFailureSurfaceChapterTasteGate :
    ChapterTasteGate RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedFailureSurfaceFromEventFlow
        (realityConstrainedFailureSurfaceToEventFlow x) = some x
    exact realityConstrainedFailureSurface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedFailureSurfaceToEventFlow_injective heq)

instance realityConstrainedFailureSurfaceFieldFaithful :
    FieldFaithful RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedFailureSurfaceFields
  field_faithful := realityConstrainedFailureSurface_fields_faithful

instance realityConstrainedFailureSurfaceNontrivial :
    Nontrivial RealityConstrainedFailureSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedFailureSurfaceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedFailureSurfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedFailureSurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedFailureSurfaceChapterTasteGate

end BEDC.Derived.RealityConstrainedFailureSurfaceUp
