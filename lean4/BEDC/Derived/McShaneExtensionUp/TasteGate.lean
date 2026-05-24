import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.McShaneExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive McShaneExtensionUp : Type where
  | mk (X A L D E S R K H C P N : BHist) : McShaneExtensionUp
  deriving DecidableEq

def mcShaneExtensionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mcShaneExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mcShaneExtensionEncodeBHist h

def mcShaneExtensionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mcShaneExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mcShaneExtensionDecodeBHist tail)

private theorem McShaneExtensionTasteGate_single_carrier_alignment_decode :
    forall h : BHist, mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mcShaneExtensionToEventFlow : McShaneExtensionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | McShaneExtensionUp.mk X A L D E S R K H C P N =>
      [mcShaneExtensionEncodeBHist X,
        mcShaneExtensionEncodeBHist A,
        mcShaneExtensionEncodeBHist L,
        mcShaneExtensionEncodeBHist D,
        mcShaneExtensionEncodeBHist E,
        mcShaneExtensionEncodeBHist S,
        mcShaneExtensionEncodeBHist R,
        mcShaneExtensionEncodeBHist K,
        mcShaneExtensionEncodeBHist H,
        mcShaneExtensionEncodeBHist C,
        mcShaneExtensionEncodeBHist P,
        mcShaneExtensionEncodeBHist N]

private def mcShaneExtensionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mcShaneExtensionEventAtDefault index rest

def mcShaneExtensionFromEventFlow (ef : EventFlow) : Option McShaneExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (McShaneExtensionUp.mk
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 0 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 1 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 2 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 3 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 4 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 5 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 6 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 7 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 8 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 9 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 10 ef))
      (mcShaneExtensionDecodeBHist (mcShaneExtensionEventAtDefault 11 ef)))

private theorem McShaneExtensionTasteGate_single_carrier_alignment_round_trip :
    forall x : McShaneExtensionUp,
      mcShaneExtensionFromEventFlow (mcShaneExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A L D E S R K H C P N =>
      change
        some
          (McShaneExtensionUp.mk
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist X))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist A))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist L))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist D))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist E))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist S))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist R))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist K))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist H))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist C))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist P))
            (mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist N))) =
          some (McShaneExtensionUp.mk X A L D E S R K H C P N)
      rw [McShaneExtensionTasteGate_single_carrier_alignment_decode X,
        McShaneExtensionTasteGate_single_carrier_alignment_decode A,
        McShaneExtensionTasteGate_single_carrier_alignment_decode L,
        McShaneExtensionTasteGate_single_carrier_alignment_decode D,
        McShaneExtensionTasteGate_single_carrier_alignment_decode E,
        McShaneExtensionTasteGate_single_carrier_alignment_decode S,
        McShaneExtensionTasteGate_single_carrier_alignment_decode R,
        McShaneExtensionTasteGate_single_carrier_alignment_decode K,
        McShaneExtensionTasteGate_single_carrier_alignment_decode H,
        McShaneExtensionTasteGate_single_carrier_alignment_decode C,
        McShaneExtensionTasteGate_single_carrier_alignment_decode P,
        McShaneExtensionTasteGate_single_carrier_alignment_decode N]

private theorem McShaneExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : McShaneExtensionUp} :
    mcShaneExtensionToEventFlow x = mcShaneExtensionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mcShaneExtensionFromEventFlow (mcShaneExtensionToEventFlow x) =
        mcShaneExtensionFromEventFlow (mcShaneExtensionToEventFlow y) :=
    congrArg mcShaneExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (McShaneExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (McShaneExtensionTasteGate_single_carrier_alignment_round_trip y)))

private def mcShaneExtensionFields : McShaneExtensionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | McShaneExtensionUp.mk X A L D E S R K H C P N => [X, A, L, D, E, S, R, K, H, C, P, N]

private theorem McShaneExtensionTasteGate_single_carrier_alignment_fields :
    forall x y : McShaneExtensionUp,
      mcShaneExtensionFields x = mcShaneExtensionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 A1 L1 D1 E1 S1 R1 K1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 L2 D2 E2 S2 R2 K2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance mcShaneExtensionBHistCarrier : BHistCarrier McShaneExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mcShaneExtensionToEventFlow
  fromEventFlow := mcShaneExtensionFromEventFlow

instance mcShaneExtensionChapterTasteGate : ChapterTasteGate McShaneExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mcShaneExtensionFromEventFlow (mcShaneExtensionToEventFlow x) = some x
    exact McShaneExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (McShaneExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance mcShaneExtensionFieldFaithful : FieldFaithful McShaneExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mcShaneExtensionFields
  field_faithful := McShaneExtensionTasteGate_single_carrier_alignment_fields

instance mcShaneExtensionNontrivial : Nontrivial McShaneExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨McShaneExtensionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      McShaneExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate McShaneExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mcShaneExtensionChapterTasteGate

theorem McShaneExtensionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate McShaneExtensionUp) ∧
      Nonempty (FieldFaithful McShaneExtensionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial McShaneExtensionUp) ∧
          (∀ h : BHist,
            mcShaneExtensionDecodeBHist (mcShaneExtensionEncodeBHist h) = h) ∧
            (∀ x : McShaneExtensionUp,
              mcShaneExtensionFromEventFlow (mcShaneExtensionToEventFlow x) = some x) ∧
              (∀ x y : McShaneExtensionUp,
                mcShaneExtensionToEventFlow x = mcShaneExtensionToEventFlow y -> x = y) ∧
                (BHistCarrier.toEventFlow
                    (McShaneExtensionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty) =
                  [mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty,
                    mcShaneExtensionEncodeBHist BHist.Empty]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨mcShaneExtensionChapterTasteGate⟩,
      ⟨mcShaneExtensionFieldFaithful⟩,
      ⟨mcShaneExtensionNontrivial⟩,
      McShaneExtensionTasteGate_single_carrier_alignment_decode,
      McShaneExtensionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => McShaneExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.McShaneExtensionUp
