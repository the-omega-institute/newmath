import BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformEpsilonTriangleHandoffUp : Type where
  | mk (X Y center x xp eps mu rho dx dxp dy dyp H C P N : BHist) :
      CompactUniformEpsilonTriangleHandoffUp
  deriving DecidableEq

def CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist h

def CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist h) =
          h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fields :
    CompactUniformEpsilonTriangleHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformEpsilonTriangleHandoffUp.mk X Y center x xp eps mu rho dx dxp dy dyp H C P N =>
      [X, Y, center, x, xp, eps, mu, rho, dx, dxp, dy, dyp, H, C, P, N]

def CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow :
    CompactUniformEpsilonTriangleHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fields token).map
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist

private def CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
        index rest

def CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CompactUniformEpsilonTriangleHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformEpsilonTriangleHandoffUp.mk
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          0 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          1 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          2 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          3 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          4 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          5 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          6 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          7 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          8 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          9 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          10 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          11 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          12 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          13 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          14 ef))
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_eventAtDefault
          15 ef)))

private theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip :
    ∀ token : CompactUniformEpsilonTriangleHandoffUp,
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fromEventFlow
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow token) =
          some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y center x xp eps mu rho dx dxp dy dyp H C P N =>
      change
        some
          (CompactUniformEpsilonTriangleHandoffUp.mk
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist X))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist Y))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
                center))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist x))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist xp))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
                eps))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist mu))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
                rho))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist dx))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
                dxp))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist dy))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
                dyp))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist H))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist C))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist P))
            (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decodeBHist
              (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CompactUniformEpsilonTriangleHandoffUp.mk X Y center x xp eps mu rho dx dxp
            dy dyp H C P N)
      rw [CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode X,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode Y,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode center,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode x,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode xp,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode eps,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode mu,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode rho,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode dx,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode dxp,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode dy,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode dyp,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode H,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode C,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode P,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformEpsilonTriangleHandoffUp} :
    CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow x =
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fromEventFlow
          (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow x) =
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fromEventFlow
          (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CompactUniformEpsilonTriangleHandoffUp,
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fields x =
          CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 center1 x1 xp1 eps1 mu1 rho1 dx1 dxp1 dy1 dyp1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 center2 x2 xp2 eps2 mu2 rho2 dx2 dxp2 dy2 dyp2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactUniformEpsilonTriangleHandoffBHistCarrier :
    BHistCarrier CompactUniformEpsilonTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow :=
    CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fromEventFlow

instance compactUniformEpsilonTriangleHandoffChapterTasteGate :
    ChapterTasteGate CompactUniformEpsilonTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro token
    change
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fromEventFlow
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow token) =
          some token
    exact CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip token
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance compactUniformEpsilonTriangleHandoffFieldFaithful :
    FieldFaithful CompactUniformEpsilonTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fields
  field_faithful :=
    CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_field_faithful

instance compactUniformEpsilonTriangleHandoffNontrivial :
    Nontrivial CompactUniformEpsilonTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformEpsilonTriangleHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformEpsilonTriangleHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactUniformEpsilonTriangleHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformEpsilonTriangleHandoffChapterTasteGate

theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactUniformEpsilonTriangleHandoffUp) ∧
      Nonempty (FieldFaithful CompactUniformEpsilonTriangleHandoffUp) ∧
        Nonempty (Nontrivial CompactUniformEpsilonTriangleHandoffUp) ∧
          CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
              BHist.Empty = [] ∧
            CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
              (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨compactUniformEpsilonTriangleHandoffChapterTasteGate⟩,
      ⟨compactUniformEpsilonTriangleHandoffFieldFaithful⟩,
      ⟨compactUniformEpsilonTriangleHandoffNontrivial⟩, rfl, rfl⟩

end BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp

namespace BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate
open BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp

theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactUniformEpsilonTriangleHandoffUp) ∧
      Nonempty (FieldFaithful CompactUniformEpsilonTriangleHandoffUp) ∧
        Nonempty (Nontrivial CompactUniformEpsilonTriangleHandoffUp) ∧
          CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
              BHist.Empty = [] ∧
            CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_encodeBHist
              (BHist.e0 BHist.Empty) = [BMark.b0] :=
  BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp.CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment

end BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp.TasteGate
