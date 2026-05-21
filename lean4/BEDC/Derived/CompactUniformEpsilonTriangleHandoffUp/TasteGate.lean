import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformEpsilonTriangleHandoffUp : Type where
  | mk (X Y center x xp eps mu rho dx dxp dy dyp H C P N : BHist) :
      CompactUniformEpsilonTriangleHandoffUp
  deriving DecidableEq

def compactUniformEpsilonTriangleHandoffEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformEpsilonTriangleHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformEpsilonTriangleHandoffEncodeBHist h

def compactUniformEpsilonTriangleHandoffDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformEpsilonTriangleHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformEpsilonTriangleHandoffDecodeBHist tail)

private theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformEpsilonTriangleHandoffFields :
    CompactUniformEpsilonTriangleHandoffUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformEpsilonTriangleHandoffUp.mk X Y center x xp eps mu rho dx dxp dy dyp H C P N =>
      [X, Y, center, x, xp, eps, mu, rho, dx, dxp, dy, dyp, H, C, P, N]

def compactUniformEpsilonTriangleHandoffToEventFlow :
    CompactUniformEpsilonTriangleHandoffUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactUniformEpsilonTriangleHandoffFields x).map
        compactUniformEpsilonTriangleHandoffEncodeBHist

private def compactUniformEpsilonTriangleHandoffEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformEpsilonTriangleHandoffEventAtDefault index rest

def compactUniformEpsilonTriangleHandoffFromEventFlow
    (ef : EventFlow) : Option CompactUniformEpsilonTriangleHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformEpsilonTriangleHandoffUp.mk
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 0 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 1 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 2 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 3 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 4 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 5 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 6 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 7 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 8 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 9 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 10 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 11 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 12 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 13 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 14 ef))
      (compactUniformEpsilonTriangleHandoffDecodeBHist
        (compactUniformEpsilonTriangleHandoffEventAtDefault 15 ef)))

private theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip :
    forall x : CompactUniformEpsilonTriangleHandoffUp,
      compactUniformEpsilonTriangleHandoffFromEventFlow
        (compactUniformEpsilonTriangleHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro packet
  cases packet with
  | mk X Y center x xp eps mu rho dx dxp dy dyp H C P N =>
      change
        some
          (CompactUniformEpsilonTriangleHandoffUp.mk
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist X))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist Y))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist center))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist x))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist xp))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist eps))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist mu))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist rho))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist dx))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist dxp))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist dy))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist dyp))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist H))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist C))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist P))
            (compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist N))) =
          some
            (CompactUniformEpsilonTriangleHandoffUp.mk
              X Y center x xp eps mu rho dx dxp dy dyp H C P N)
      rw [CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode X,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode Y,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode center,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode x,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode xp,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode eps,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode mu,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode rho,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode dx,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode dxp,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode dy,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode dyp,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode H,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode C,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode P,
        CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformEpsilonTriangleHandoffToEventFlow_injective
    {x y : CompactUniformEpsilonTriangleHandoffUp} :
    compactUniformEpsilonTriangleHandoffToEventFlow x =
      compactUniformEpsilonTriangleHandoffToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformEpsilonTriangleHandoffFromEventFlow
          (compactUniformEpsilonTriangleHandoffToEventFlow x) =
        compactUniformEpsilonTriangleHandoffFromEventFlow
          (compactUniformEpsilonTriangleHandoffToEventFlow y) :=
    congrArg compactUniformEpsilonTriangleHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fields :
    forall x y : CompactUniformEpsilonTriangleHandoffUp,
      compactUniformEpsilonTriangleHandoffFields x =
        compactUniformEpsilonTriangleHandoffFields y -> x = y := by
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
  toEventFlow := compactUniformEpsilonTriangleHandoffToEventFlow
  fromEventFlow := compactUniformEpsilonTriangleHandoffFromEventFlow

instance compactUniformEpsilonTriangleHandoffChapterTasteGate :
    ChapterTasteGate CompactUniformEpsilonTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformEpsilonTriangleHandoffFromEventFlow
        (compactUniformEpsilonTriangleHandoffToEventFlow x) = some x
    exact CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactUniformEpsilonTriangleHandoffToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactUniformEpsilonTriangleHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformEpsilonTriangleHandoffChapterTasteGate

instance compactUniformEpsilonTriangleHandoffFieldFaithful :
    FieldFaithful CompactUniformEpsilonTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformEpsilonTriangleHandoffFields
  field_faithful :=
    CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_fields

instance compactUniformEpsilonTriangleHandoffNontrivial :
    Nontrivial CompactUniformEpsilonTriangleHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformEpsilonTriangleHandoffUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CompactUniformEpsilonTriangleHandoffUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactUniformEpsilonTriangleHandoffUp) ∧
      Nonempty (FieldFaithful CompactUniformEpsilonTriangleHandoffUp) ∧
        Nonempty (Nontrivial CompactUniformEpsilonTriangleHandoffUp) ∧
          (∀ h : BHist,
            compactUniformEpsilonTriangleHandoffDecodeBHist
              (compactUniformEpsilonTriangleHandoffEncodeBHist h) = h) ∧
            (∀ x : CompactUniformEpsilonTriangleHandoffUp,
              compactUniformEpsilonTriangleHandoffFromEventFlow
                (compactUniformEpsilonTriangleHandoffToEventFlow x) = some x) ∧
              (∀ x y : CompactUniformEpsilonTriangleHandoffUp,
                compactUniformEpsilonTriangleHandoffToEventFlow x =
                  compactUniformEpsilonTriangleHandoffToEventFlow y -> x = y) ∧
                compactUniformEpsilonTriangleHandoffEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨compactUniformEpsilonTriangleHandoffChapterTasteGate⟩,
      ⟨compactUniformEpsilonTriangleHandoffFieldFaithful⟩,
      ⟨compactUniformEpsilonTriangleHandoffNontrivial⟩,
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_decode,
      CompactUniformEpsilonTriangleHandoffTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompactUniformEpsilonTriangleHandoffToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactUniformEpsilonTriangleHandoffUp.TasteGate
