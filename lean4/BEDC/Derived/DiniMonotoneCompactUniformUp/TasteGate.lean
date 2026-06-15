import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniMonotoneCompactUniformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniMonotoneCompactUniformUp : Type where
  | mk (X F M L R V U H C P N : BHist) : DiniMonotoneCompactUniformUp
  deriving DecidableEq

def diniMonotoneCompactUniformEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniMonotoneCompactUniformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniMonotoneCompactUniformEncodeBHist h

def diniMonotoneCompactUniformDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniMonotoneCompactUniformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniMonotoneCompactUniformDecodeBHist tail)

private theorem DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      diniMonotoneCompactUniformDecodeBHist
          (diniMonotoneCompactUniformEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diniMonotoneCompactUniformFields :
    DiniMonotoneCompactUniformUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniMonotoneCompactUniformUp.mk X F M L R V U H C P N =>
      [X, F, M, L, R, V, U, H, C, P, N]

def diniMonotoneCompactUniformToEventFlow :
    DiniMonotoneCompactUniformUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (diniMonotoneCompactUniformFields x).map
      diniMonotoneCompactUniformEncodeBHist

private def diniMonotoneCompactUniformEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      diniMonotoneCompactUniformEventAtDefault index rest

def diniMonotoneCompactUniformFromEventFlow
    (ef : EventFlow) : Option DiniMonotoneCompactUniformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiniMonotoneCompactUniformUp.mk
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 0 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 1 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 2 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 3 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 4 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 5 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 6 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 7 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 8 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 9 ef))
      (diniMonotoneCompactUniformDecodeBHist
        (diniMonotoneCompactUniformEventAtDefault 10 ef)))

private theorem DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_round_trip :
    forall x : DiniMonotoneCompactUniformUp,
      diniMonotoneCompactUniformFromEventFlow
          (diniMonotoneCompactUniformToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X F M L R V U H C P N =>
      change
        some
          (DiniMonotoneCompactUniformUp.mk
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist X))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist F))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist M))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist L))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist R))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist V))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist U))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist H))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist C))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist P))
            (diniMonotoneCompactUniformDecodeBHist
              (diniMonotoneCompactUniformEncodeBHist N))) =
          some (DiniMonotoneCompactUniformUp.mk X F M L R V U H C P N)
      rw [DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode X,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode F,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode M,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode L,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode R,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode V,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode U,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode H,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode C,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode P,
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode N]

private theorem DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiniMonotoneCompactUniformUp} :
    diniMonotoneCompactUniformToEventFlow x =
      diniMonotoneCompactUniformToEventFlow y ->
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniMonotoneCompactUniformFromEventFlow
          (diniMonotoneCompactUniformToEventFlow x) =
        diniMonotoneCompactUniformFromEventFlow
          (diniMonotoneCompactUniformToEventFlow y) :=
    congrArg diniMonotoneCompactUniformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_fields :
    forall x y : DiniMonotoneCompactUniformUp,
      diniMonotoneCompactUniformFields x = diniMonotoneCompactUniformFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 F1 M1 L1 R1 V1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 M2 L2 R2 V2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance diniMonotoneCompactUniformBHistCarrier :
    BHistCarrier DiniMonotoneCompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniMonotoneCompactUniformToEventFlow
  fromEventFlow := diniMonotoneCompactUniformFromEventFlow

instance diniMonotoneCompactUniformChapterTasteGate :
    ChapterTasteGate DiniMonotoneCompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      diniMonotoneCompactUniformFromEventFlow
          (diniMonotoneCompactUniformToEventFlow x) =
        some x
    exact DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance diniMonotoneCompactUniformFieldFaithful :
    FieldFaithful DiniMonotoneCompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diniMonotoneCompactUniformFields
  field_faithful := DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_fields

instance diniMonotoneCompactUniformNontrivial :
    Nontrivial DiniMonotoneCompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiniMonotoneCompactUniformUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DiniMonotoneCompactUniformUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiniMonotoneCompactUniformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diniMonotoneCompactUniformChapterTasteGate

theorem DiniMonotoneCompactUniformTasteGate_single_carrier_alignment :
    (forall h : BHist,
      diniMonotoneCompactUniformDecodeBHist
          (diniMonotoneCompactUniformEncodeBHist h) =
        h) ∧
      (forall x : DiniMonotoneCompactUniformUp,
        diniMonotoneCompactUniformFromEventFlow
            (diniMonotoneCompactUniformToEventFlow x) =
          some x) ∧
        (forall x y : DiniMonotoneCompactUniformUp,
          diniMonotoneCompactUniformToEventFlow x =
            diniMonotoneCompactUniformToEventFlow y ->
          x = y) ∧
          diniMonotoneCompactUniformEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_decode,
      DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DiniMonotoneCompactUniformTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.DiniMonotoneCompactUniformUp
