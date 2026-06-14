import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LusinApproximationUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LusinApproximationUp : Type where
  | mk (M A C F E I R H Q P N : BHist) : LusinApproximationUp
  deriving DecidableEq

def lusinApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lusinApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lusinApproximationEncodeBHist h

def lusinApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lusinApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lusinApproximationDecodeBHist tail)

private theorem LusinApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      lusinApproximationDecodeBHist (lusinApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lusinApproximationFields : LusinApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LusinApproximationUp.mk M A C F E I R H Q P N => [M, A, C, F, E, I, R, H, Q, P, N]

def lusinApproximationToEventFlow : LusinApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lusinApproximationFields x).map lusinApproximationEncodeBHist

def lusinApproximationFromEventFlow : EventFlow → Option LusinApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | A :: restA =>
          match restA with
          | C :: restC =>
              match restC with
              | F :: restF =>
                  match restF with
                  | E :: restE =>
                      match restE with
                      | I :: restI =>
                          match restI with
                          | R :: restR =>
                              match restR with
                              | H :: restH =>
                                  match restH with
                                  | Q :: restQ =>
                                      match restQ with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (LusinApproximationUp.mk
                                                      (lusinApproximationDecodeBHist M)
                                                      (lusinApproximationDecodeBHist A)
                                                      (lusinApproximationDecodeBHist C)
                                                      (lusinApproximationDecodeBHist F)
                                                      (lusinApproximationDecodeBHist E)
                                                      (lusinApproximationDecodeBHist I)
                                                      (lusinApproximationDecodeBHist R)
                                                      (lusinApproximationDecodeBHist H)
                                                      (lusinApproximationDecodeBHist Q)
                                                      (lusinApproximationDecodeBHist P)
                                                      (lusinApproximationDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem LusinApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LusinApproximationUp,
      lusinApproximationFromEventFlow (lusinApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M A C F E I R H Q P N =>
      change
        some
            (LusinApproximationUp.mk
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist M))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist A))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist C))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist F))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist E))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist I))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist R))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist H))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist Q))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist P))
              (lusinApproximationDecodeBHist (lusinApproximationEncodeBHist N))) =
          some (LusinApproximationUp.mk M A C F E I R H Q P N)
      rw [LusinApproximationTasteGate_single_carrier_alignment_decode M,
        LusinApproximationTasteGate_single_carrier_alignment_decode A,
        LusinApproximationTasteGate_single_carrier_alignment_decode C,
        LusinApproximationTasteGate_single_carrier_alignment_decode F,
        LusinApproximationTasteGate_single_carrier_alignment_decode E,
        LusinApproximationTasteGate_single_carrier_alignment_decode I,
        LusinApproximationTasteGate_single_carrier_alignment_decode R,
        LusinApproximationTasteGate_single_carrier_alignment_decode H,
        LusinApproximationTasteGate_single_carrier_alignment_decode Q,
        LusinApproximationTasteGate_single_carrier_alignment_decode P,
        LusinApproximationTasteGate_single_carrier_alignment_decode N]

private theorem lusinApproximationToEventFlow_injective {x y : LusinApproximationUp} :
    lusinApproximationToEventFlow x = lusinApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lusinApproximationFromEventFlow (lusinApproximationToEventFlow x) =
        lusinApproximationFromEventFlow (lusinApproximationToEventFlow y) :=
    congrArg lusinApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LusinApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LusinApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem lusinApproximation_field_faithful :
    ∀ x y : LusinApproximationUp,
      lusinApproximationFields x = lusinApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M A C F E I R H Q P N =>
      cases y with
      | mk M' A' C' F' E' I' R' H' Q' P' N' =>
          cases hfields
          rfl

instance lusinApproximationBHistCarrier : BHistCarrier LusinApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lusinApproximationToEventFlow
  fromEventFlow := lusinApproximationFromEventFlow

instance lusinApproximationChapterTasteGate : ChapterTasteGate LusinApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lusinApproximationFromEventFlow (lusinApproximationToEventFlow x) = some x
    exact LusinApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lusinApproximationToEventFlow_injective heq)

instance lusinApproximationFieldFaithful : FieldFaithful LusinApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lusinApproximationFields
  field_faithful := lusinApproximation_field_faithful

instance lusinApproximationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LusinApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LusinApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LusinApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LusinApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lusinApproximationChapterTasteGate

theorem LusinApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LusinApproximationUp) ∧
      Nonempty (FieldFaithful LusinApproximationUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LusinApproximationUp) ∧
      (∀ h : BHist, lusinApproximationDecodeBHist (lusinApproximationEncodeBHist h) = h) ∧
      (∀ x : LusinApproximationUp,
        lusinApproximationFromEventFlow (lusinApproximationToEventFlow x) = some x) ∧
      lusinApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨lusinApproximationChapterTasteGate⟩
  constructor
  · exact ⟨lusinApproximationFieldFaithful⟩
  constructor
  · exact ⟨lusinApproximationNontrivial⟩
  constructor
  · exact LusinApproximationTasteGate_single_carrier_alignment_decode
  constructor
  · exact LusinApproximationTasteGate_single_carrier_alignment_round_trip
  · rfl

end TasteGate
end BEDC.Derived.LusinApproximationUp
