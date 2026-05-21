import BEDC.Derived.DiagonalIndexCofinalityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalIndexCofinalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalIndexCofinalityUp : Type where
  | mk (X modulus request threshold selectedIndex window readback dyadicLedger realHandoff
      transport route provenance nameCert : BHist) : DiagonalIndexCofinalityUp
  deriving DecidableEq

def DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist h

def DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fields :
    DiagonalIndexCofinalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalIndexCofinalityUp.mk X modulus request threshold selectedIndex window readback
      dyadicLedger realHandoff transport route provenance nameCert =>
      [X, modulus, request, threshold, selectedIndex, window, readback, dyadicLedger,
        realHandoff, transport, route, provenance, nameCert]

def DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow :
    DiagonalIndexCofinalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fields token).map
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist

private def DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault index rest

def DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option DiagonalIndexCofinalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiagonalIndexCofinalityUp.mk
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

private theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip :
    ∀ token : DiagonalIndexCofinalityUp,
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fromEventFlow
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow token) =
          some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X modulus request threshold selectedIndex window readback dyadicLedger realHandoff
      transport route provenance nameCert =>
      change
        some
          (DiagonalIndexCofinalityUp.mk
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist X))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist modulus))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist request))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist threshold))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist
                selectedIndex))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist window))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist readback))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist
                dyadicLedger))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist
                realHandoff))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist transport))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist route))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist provenance))
            (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decodeBHist
              (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist nameCert))) =
          some
            (DiagonalIndexCofinalityUp.mk X modulus request threshold selectedIndex window readback
              dyadicLedger realHandoff transport route provenance nameCert)
      rw [DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode X,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode modulus,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode request,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode threshold,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode selectedIndex,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode window,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode readback,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode realHandoff,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode transport,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode route,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode provenance,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiagonalIndexCofinalityUp} :
    DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow x =
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fromEventFlow
          (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow x) =
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fromEventFlow
          (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DiagonalIndexCofinalityUp,
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fields x =
          DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 modulus1 request1 threshold1 selectedIndex1 window1 readback1 dyadicLedger1
      realHandoff1 transport1 route1 provenance1 nameCert1 =>
      cases y with
      | mk X2 modulus2 request2 threshold2 selectedIndex2 window2 readback2 dyadicLedger2
          realHandoff2 transport2 route2 provenance2 nameCert2 =>
          cases hfields
          rfl

instance diagonalIndexCofinalityBHistCarrier : BHistCarrier DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fromEventFlow

instance diagonalIndexCofinalityChapterTasteGate : ChapterTasteGate DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro token
    change
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fromEventFlow
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow token) = some token
    exact DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip token
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance diagonalIndexCofinalityFieldFaithful : FieldFaithful DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fields
  field_faithful := DiagonalIndexCofinalityTasteGate_single_carrier_alignment_field_faithful

instance diagonalIndexCofinalityNontrivial : Nontrivial DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalIndexCofinalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DiagonalIndexCofinalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiagonalIndexCofinalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalIndexCofinalityChapterTasteGate

theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DiagonalIndexCofinalityUp) ∧
      Nonempty (FieldFaithful DiagonalIndexCofinalityUp) ∧
        Nonempty (Nontrivial DiagonalIndexCofinalityUp) ∧
          DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
              [] ∧
            DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist
              (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨diagonalIndexCofinalityChapterTasteGate⟩,
      ⟨diagonalIndexCofinalityFieldFaithful⟩,
      ⟨diagonalIndexCofinalityNontrivial⟩, rfl, rfl⟩

end BEDC.Derived.DiagonalIndexCofinalityUp

namespace BEDC.Derived.DiagonalIndexCofinalityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate
open BEDC.Derived.DiagonalIndexCofinalityUp

theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DiagonalIndexCofinalityUp) ∧
      Nonempty (FieldFaithful DiagonalIndexCofinalityUp) ∧
        Nonempty (Nontrivial DiagonalIndexCofinalityUp) ∧
          DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
              [] ∧
            DiagonalIndexCofinalityTasteGate_single_carrier_alignment_encodeBHist
              (BHist.e0 BHist.Empty) = [BMark.b0] :=
  BEDC.Derived.DiagonalIndexCofinalityUp.DiagonalIndexCofinalityTasteGate_single_carrier_alignment

end BEDC.Derived.DiagonalIndexCofinalityUp.TasteGate
