import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyBornologicalUniformityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyBornologicalUniformityUp : Type where
  | mk (F B M U C H R P N : BHist) : CauchyBornologicalUniformityUp
  deriving DecidableEq

def cauchyBornologicalUniformityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyBornologicalUniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyBornologicalUniformityEncodeBHist h

def cauchyBornologicalUniformityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyBornologicalUniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyBornologicalUniformityDecodeBHist tail)

private theorem CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchyBornologicalUniformityDecodeBHist
          (cauchyBornologicalUniformityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyBornologicalUniformityFields :
    CauchyBornologicalUniformityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyBornologicalUniformityUp.mk F B M U C H R P N =>
      [F, B, M, U, C, H, R, P, N]

def cauchyBornologicalUniformityToEventFlow :
    CauchyBornologicalUniformityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyBornologicalUniformityFields x).map
      cauchyBornologicalUniformityEncodeBHist

private def cauchyBornologicalUniformityEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyBornologicalUniformityEventAtDefault index rest

def cauchyBornologicalUniformityFromEventFlow
    (ef : EventFlow) : Option CauchyBornologicalUniformityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyBornologicalUniformityUp.mk
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 0 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 1 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 2 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 3 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 4 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 5 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 6 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 7 ef))
      (cauchyBornologicalUniformityDecodeBHist
        (cauchyBornologicalUniformityEventAtDefault 8 ef)))

private theorem CauchyBornologicalUniformityTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyBornologicalUniformityUp,
      cauchyBornologicalUniformityFromEventFlow
          (cauchyBornologicalUniformityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B M U C H R P N =>
      change
        some
          (CauchyBornologicalUniformityUp.mk
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist F))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist B))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist M))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist U))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist C))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist H))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist R))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist P))
            (cauchyBornologicalUniformityDecodeBHist
              (cauchyBornologicalUniformityEncodeBHist N))) =
          some (CauchyBornologicalUniformityUp.mk F B M U C H R P N)
      rw [CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode F,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode B,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode M,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode U,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode C,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode H,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode R,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode P,
        CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode N]

private theorem CauchyBornologicalUniformityToEventFlow_injective
    {x y : CauchyBornologicalUniformityUp} :
    cauchyBornologicalUniformityToEventFlow x =
        cauchyBornologicalUniformityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyBornologicalUniformityFromEventFlow
          (cauchyBornologicalUniformityToEventFlow x) =
        cauchyBornologicalUniformityFromEventFlow
          (cauchyBornologicalUniformityToEventFlow y) :=
    congrArg cauchyBornologicalUniformityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyBornologicalUniformityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyBornologicalUniformityTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyBornologicalUniformity_field_faithful :
    forall x y : CauchyBornologicalUniformityUp,
      cauchyBornologicalUniformityFields x =
          cauchyBornologicalUniformityFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 B1 M1 U1 C1 H1 R1 P1 N1 =>
      cases y with
      | mk F2 B2 M2 U2 C2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance cauchyBornologicalUniformityBHistCarrier :
    BHistCarrier CauchyBornologicalUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyBornologicalUniformityToEventFlow
  fromEventFlow := cauchyBornologicalUniformityFromEventFlow

instance cauchyBornologicalUniformityChapterTasteGate :
    ChapterTasteGate CauchyBornologicalUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyBornologicalUniformityFromEventFlow
          (cauchyBornologicalUniformityToEventFlow x) =
        some x
    exact CauchyBornologicalUniformityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyBornologicalUniformityToEventFlow_injective heq)

instance cauchyBornologicalUniformityFieldFaithful :
    FieldFaithful CauchyBornologicalUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyBornologicalUniformityFields
  field_faithful := CauchyBornologicalUniformity_field_faithful

instance cauchyBornologicalUniformityNontrivial :
    Nontrivial CauchyBornologicalUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyBornologicalUniformityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyBornologicalUniformityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyBornologicalUniformityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyBornologicalUniformityUp) ∧
      (∀ h : BHist,
        cauchyBornologicalUniformityDecodeBHist
            (cauchyBornologicalUniformityEncodeBHist h) =
          h) ∧
      (∀ x : CauchyBornologicalUniformityUp,
        cauchyBornologicalUniformityFromEventFlow
            (cauchyBornologicalUniformityToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyBornologicalUniformityUp,
        cauchyBornologicalUniformityToEventFlow x =
            cauchyBornologicalUniformityToEventFlow y ->
          x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨cauchyBornologicalUniformityChapterTasteGate⟩,
      CauchyBornologicalUniformityTasteGate_single_carrier_alignment_decode,
      CauchyBornologicalUniformityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyBornologicalUniformityToEventFlow_injective heq)⟩

end BEDC.Derived.CauchyBornologicalUniformityUp.TasteGate
