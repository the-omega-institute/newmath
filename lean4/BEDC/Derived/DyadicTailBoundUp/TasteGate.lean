import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicTailBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicTailBoundUp : Type where
  | mk (p mu epsilon L R E H C P N : BHist) : DyadicTailBoundUp
  deriving DecidableEq

def dyadicTailBoundEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicTailBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicTailBoundEncodeBHist h

def dyadicTailBoundDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicTailBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicTailBoundDecodeBHist tail)

private theorem DyadicTailBoundTasteGate_single_carrier_alignment_decode :
    forall h : BHist, dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicTailBoundToEventFlow : DyadicTailBoundUp -> EventFlow
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

private def dyadicTailBoundEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicTailBoundEventAtDefault index rest

def dyadicTailBoundFromEventFlow (ef : EventFlow) : Option DyadicTailBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicTailBoundUp.mk
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 1 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 3 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 5 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 7 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 9 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 11 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 13 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 15 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 17 ef))
      (dyadicTailBoundDecodeBHist (dyadicTailBoundEventAtDefault 19 ef)))

private theorem DyadicTailBoundTasteGate_single_carrier_alignment_round_trip :
    forall x : DyadicTailBoundUp,
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
      rw [DyadicTailBoundTasteGate_single_carrier_alignment_decode p,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode mu,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode epsilon,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode L,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode R,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode E,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode H,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode C,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode P,
        DyadicTailBoundTasteGate_single_carrier_alignment_decode N]

private theorem DyadicTailBoundTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicTailBoundUp} :
    dyadicTailBoundToEventFlow x = dyadicTailBoundToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow x) =
        dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow y) :=
    congrArg dyadicTailBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicTailBoundTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicTailBoundTasteGate_single_carrier_alignment_round_trip y)))

private def dyadicTailBoundFields : DyadicTailBoundUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicTailBoundUp.mk p mu epsilon L R E H C P N => [p, mu, epsilon, L, R, E, H, C, P, N]

private theorem DyadicTailBoundTasteGate_single_carrier_alignment_fields :
    forall x y : DyadicTailBoundUp, dyadicTailBoundFields x = dyadicTailBoundFields y -> x = y := by
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
    exact DyadicTailBoundTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicTailBoundTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicTailBoundFieldFaithful : FieldFaithful DyadicTailBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicTailBoundFields
  field_faithful := DyadicTailBoundTasteGate_single_carrier_alignment_fields

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

def taste_gate : ChapterTasteGate DyadicTailBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicTailBoundChapterTasteGate

theorem DyadicTailBoundTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicTailBoundUp) ∧
      Nonempty (FieldFaithful DyadicTailBoundUp) ∧
        Nonempty (Nontrivial DyadicTailBoundUp) ∧
          (forall h : BHist, dyadicTailBoundDecodeBHist (dyadicTailBoundEncodeBHist h) = h) ∧
            (forall x : DyadicTailBoundUp,
              dyadicTailBoundFromEventFlow (dyadicTailBoundToEventFlow x) = some x) ∧
              (forall x y : DyadicTailBoundUp,
                dyadicTailBoundToEventFlow x = dyadicTailBoundToEventFlow y -> x = y) ∧
                dyadicTailBoundEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨dyadicTailBoundChapterTasteGate⟩,
      ⟨dyadicTailBoundFieldFaithful⟩,
      ⟨dyadicTailBoundNontrivial⟩,
      DyadicTailBoundTasteGate_single_carrier_alignment_decode,
      DyadicTailBoundTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DyadicTailBoundTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicTailBoundUp
