import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicPoissonKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicPoissonKernelUp : Type where
  | mk (D M B V U S I R W H C P N : BHist) : HyperbolicPoissonKernelUp
  deriving DecidableEq

def hyperbolicPoissonKernelEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicPoissonKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicPoissonKernelEncodeBHist h

def hyperbolicPoissonKernelDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicPoissonKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicPoissonKernelDecodeBHist tail)

private theorem HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicPoissonKernelFields :
    HyperbolicPoissonKernelUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicPoissonKernelUp.mk D M B V U S I R W H C P N =>
      [D, M, B, V, U, S, I, R, W, H, C, P, N]

def hyperbolicPoissonKernelToEventFlow :
    HyperbolicPoissonKernelUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicPoissonKernelFields x).map hyperbolicPoissonKernelEncodeBHist

private def hyperbolicPoissonKernelEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hyperbolicPoissonKernelEventAtDefault index rest

def hyperbolicPoissonKernelFromEventFlow :
    EventFlow -> Option HyperbolicPoissonKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (HyperbolicPoissonKernelUp.mk
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 0 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 1 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 2 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 3 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 4 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 5 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 6 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 7 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 8 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 9 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 10 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 11 ef))
        (hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEventAtDefault 12 ef)))

private theorem HyperbolicPoissonKernelTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicPoissonKernelUp) :
    hyperbolicPoissonKernelFromEventFlow
        (hyperbolicPoissonKernelToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D M B V U S I R W H C P N =>
      change
        some
          (HyperbolicPoissonKernelUp.mk
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist D))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist M))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist B))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist V))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist U))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist S))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist I))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist R))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist W))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist H))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist C))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist P))
            (hyperbolicPoissonKernelDecodeBHist
              (hyperbolicPoissonKernelEncodeBHist N))) =
          some (HyperbolicPoissonKernelUp.mk D M B V U S I R W H C P N)
      rw [HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode D,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode M,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode B,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode V,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode U,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode S,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode I,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode R,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode W,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode H,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode C,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode P,
        HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperbolicPoissonKernelTasteGate_single_carrier_alignment_injective
    {x y : HyperbolicPoissonKernelUp} :
    hyperbolicPoissonKernelToEventFlow x =
        hyperbolicPoissonKernelToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicPoissonKernelFromEventFlow
          (hyperbolicPoissonKernelToEventFlow x) =
        hyperbolicPoissonKernelFromEventFlow
          (hyperbolicPoissonKernelToEventFlow y) :=
    congrArg hyperbolicPoissonKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicPoissonKernelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicPoissonKernelTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicPoissonKernelTasteGate_single_carrier_alignment_fields :
    forall x y : HyperbolicPoissonKernelUp,
      hyperbolicPoissonKernelFields x =
        hyperbolicPoissonKernelFields y ->
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 M1 B1 V1 U1 S1 I1 R1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 M2 B2 V2 U2 S2 I2 R2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicPoissonKernelBHistCarrier :
    BHistCarrier HyperbolicPoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicPoissonKernelToEventFlow
  fromEventFlow := hyperbolicPoissonKernelFromEventFlow

instance hyperbolicPoissonKernelChapterTasteGate :
    ChapterTasteGate HyperbolicPoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicPoissonKernelFromEventFlow
          (hyperbolicPoissonKernelToEventFlow x) =
        some x
    exact HyperbolicPoissonKernelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicPoissonKernelTasteGate_single_carrier_alignment_injective heq)

instance hyperbolicPoissonKernelFieldFaithful :
    FieldFaithful HyperbolicPoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicPoissonKernelFields
  field_faithful := HyperbolicPoissonKernelTasteGate_single_carrier_alignment_fields

instance hyperbolicPoissonKernelNontrivial :
    Nontrivial HyperbolicPoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicPoissonKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicPoissonKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicPoissonKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicPoissonKernelChapterTasteGate

theorem HyperbolicPoissonKernelTasteGate_single_carrier_alignment :
    (forall h : BHist,
      hyperbolicPoissonKernelDecodeBHist
          (hyperbolicPoissonKernelEncodeBHist h) =
        h) ∧
      (forall x : HyperbolicPoissonKernelUp,
        hyperbolicPoissonKernelFromEventFlow
            (hyperbolicPoissonKernelToEventFlow x) =
          some x) ∧
        (forall x y : HyperbolicPoissonKernelUp,
          hyperbolicPoissonKernelToEventFlow x =
              hyperbolicPoissonKernelToEventFlow y ->
            x = y) ∧
          (forall x y : HyperbolicPoissonKernelUp,
            hyperbolicPoissonKernelFields x =
                hyperbolicPoissonKernelFields y ->
              x = y) ∧
            (exists x y : HyperbolicPoissonKernelUp, x ≠ y) ∧
              hyperbolicPoissonKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HyperbolicPoissonKernelTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HyperbolicPoissonKernelTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HyperbolicPoissonKernelTasteGate_single_carrier_alignment_injective heq
      · constructor
        · exact HyperbolicPoissonKernelTasteGate_single_carrier_alignment_fields
        · constructor
          · exact
              ⟨HyperbolicPoissonKernelUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                HyperbolicPoissonKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩
          · rfl

end BEDC.Derived.HyperbolicPoissonKernelUp
