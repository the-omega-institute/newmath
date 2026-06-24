import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApophaticBoundarySocketStackUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApophaticBoundarySocketStackUp : Type where
  | mk (T KD L F A V R H C P N : BHist) : ApophaticBoundarySocketStackUp
  deriving DecidableEq

def apophaticBoundarySocketStackEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apophaticBoundarySocketStackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apophaticBoundarySocketStackEncodeBHist h

def apophaticBoundarySocketStackDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apophaticBoundarySocketStackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apophaticBoundarySocketStackDecodeBHist tail)

private theorem ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apophaticBoundarySocketStackFields :
    ApophaticBoundarySocketStackUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticBoundarySocketStackUp.mk T KD L F A V R H C P N =>
      [T, KD, L, F, A, V, R, H, C, P, N]

def apophaticBoundarySocketStackToEventFlow :
    ApophaticBoundarySocketStackUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (apophaticBoundarySocketStackFields x).map
        apophaticBoundarySocketStackEncodeBHist

private def apophaticBoundarySocketStackEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      apophaticBoundarySocketStackEventAtDefault index rest

def apophaticBoundarySocketStackFromEventFlow
    (ef : EventFlow) : Option ApophaticBoundarySocketStackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ApophaticBoundarySocketStackUp.mk
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 0 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 1 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 2 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 3 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 4 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 5 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 6 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 7 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 8 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 9 ef))
      (apophaticBoundarySocketStackDecodeBHist
        (apophaticBoundarySocketStackEventAtDefault 10 ef)))

private theorem ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_round_trip
    (x : ApophaticBoundarySocketStackUp) :
    apophaticBoundarySocketStackFromEventFlow
      (apophaticBoundarySocketStackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T KD L F A V R H C P N =>
      change
        some
          (ApophaticBoundarySocketStackUp.mk
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist T))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist KD))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist L))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist F))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist A))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist V))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist R))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist H))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist C))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist P))
            (apophaticBoundarySocketStackDecodeBHist
              (apophaticBoundarySocketStackEncodeBHist N))) =
          some (ApophaticBoundarySocketStackUp.mk T KD L F A V R H C P N)
      rw [ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode T,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode KD,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode L,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode F,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode A,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode V,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode R,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode H,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode C,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode P,
        ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode N]

private theorem ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_injective
    {x y : ApophaticBoundarySocketStackUp} :
    apophaticBoundarySocketStackToEventFlow x =
      apophaticBoundarySocketStackToEventFlow y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apophaticBoundarySocketStackFromEventFlow
          (apophaticBoundarySocketStackToEventFlow x) =
        apophaticBoundarySocketStackFromEventFlow
          (apophaticBoundarySocketStackToEventFlow y) :=
    congrArg apophaticBoundarySocketStackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_round_trip y)))

private theorem ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_fields :
    forall x y : ApophaticBoundarySocketStackUp,
      apophaticBoundarySocketStackFields x =
        apophaticBoundarySocketStackFields y ->
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 KD1 L1 F1 A1 V1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 KD2 L2 F2 A2 V2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance apophaticBoundarySocketStackBHistCarrier :
    BHistCarrier ApophaticBoundarySocketStackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apophaticBoundarySocketStackToEventFlow
  fromEventFlow := apophaticBoundarySocketStackFromEventFlow

instance apophaticBoundarySocketStackChapterTasteGate :
    ChapterTasteGate ApophaticBoundarySocketStackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      apophaticBoundarySocketStackFromEventFlow
        (apophaticBoundarySocketStackToEventFlow x) = some x
    exact ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_injective heq)

instance apophaticBoundarySocketStackFieldFaithful :
    FieldFaithful ApophaticBoundarySocketStackUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apophaticBoundarySocketStackFields
  field_faithful :=
    ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_fields

instance apophaticBoundarySocketStackNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ApophaticBoundarySocketStackUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApophaticBoundarySocketStackUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ApophaticBoundarySocketStackUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ApophaticBoundarySocketStackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apophaticBoundarySocketStackChapterTasteGate

theorem ApophaticBoundarySocketStackTasteGate_single_carrier_alignment
    (T KD L F A V R H C P N : BHist) :
    apophaticBoundarySocketStackDecodeBHist
        (BMark.b0 :: apophaticBoundarySocketStackEncodeBHist T) =
      BHist.e0 T ∧
    apophaticBoundarySocketStackFromEventFlow
        (apophaticBoundarySocketStackToEventFlow
          (ApophaticBoundarySocketStackUp.mk T KD L F A V R H C P N)) =
      some (ApophaticBoundarySocketStackUp.mk T KD L F A V R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact congrArg BHist.e0
      (ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_decode_encode T)
  · exact ApophaticBoundarySocketStackTasteGate_single_carrier_alignment_round_trip
      (ApophaticBoundarySocketStackUp.mk T KD L F A V R H C P N)

end BEDC.Derived.ApophaticBoundarySocketStackUp
