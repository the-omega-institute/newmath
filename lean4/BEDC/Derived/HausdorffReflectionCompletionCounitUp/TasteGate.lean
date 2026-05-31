import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffReflectionCompletionCounitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffReflectionCompletionCounitUp : Type where
  | mk (U V R S W Q D E H C P N : BHist) : HausdorffReflectionCompletionCounitUp
  deriving DecidableEq

def hausdorffReflectionCompletionCounitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffReflectionCompletionCounitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffReflectionCompletionCounitEncodeBHist h

def hausdorffReflectionCompletionCounitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffReflectionCompletionCounitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffReflectionCompletionCounitDecodeBHist tail)

private theorem HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hausdorffReflectionCompletionCounitDecodeBHist
        (hausdorffReflectionCompletionCounitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffReflectionCompletionCounitToEventFlow :
    HausdorffReflectionCompletionCounitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffReflectionCompletionCounitUp.mk U V R S W Q D E H C P N =>
      [hausdorffReflectionCompletionCounitEncodeBHist U,
        hausdorffReflectionCompletionCounitEncodeBHist V,
        hausdorffReflectionCompletionCounitEncodeBHist R,
        hausdorffReflectionCompletionCounitEncodeBHist S,
        hausdorffReflectionCompletionCounitEncodeBHist W,
        hausdorffReflectionCompletionCounitEncodeBHist Q,
        hausdorffReflectionCompletionCounitEncodeBHist D,
        hausdorffReflectionCompletionCounitEncodeBHist E,
        hausdorffReflectionCompletionCounitEncodeBHist H,
        hausdorffReflectionCompletionCounitEncodeBHist C,
        hausdorffReflectionCompletionCounitEncodeBHist P,
        hausdorffReflectionCompletionCounitEncodeBHist N]

def hausdorffReflectionCompletionCounitFromEventFlow :
    EventFlow → Option HausdorffReflectionCompletionCounitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: restU =>
      match restU with
      | [] => none
      | V :: restV =>
          match restV with
          | [] => none
          | R :: restR =>
              match restR with
              | [] => none
              | S :: restS =>
                  match restS with
                  | [] => none
                  | W :: restW =>
                      match restW with
                      | [] => none
                      | Q :: restQ =>
                          match restQ with
                          | [] => none
                          | D :: restD =>
                              match restD with
                              | [] => none
                              | E :: restE =>
                                  match restE with
                                  | [] => none
                                  | H :: restH =>
                                      match restH with
                                      | [] => none
                                      | C :: restC =>
                                          match restC with
                                          | [] => none
                                          | P :: restP =>
                                              match restP with
                                              | [] => none
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (HausdorffReflectionCompletionCounitUp.mk
                                                          (hausdorffReflectionCompletionCounitDecodeBHist U)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist V)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist R)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist S)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist W)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist Q)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist D)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist E)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist H)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist C)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist P)
                                                          (hausdorffReflectionCompletionCounitDecodeBHist N))
                                                  | _ :: _ => none

private theorem HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffReflectionCompletionCounitUp,
      hausdorffReflectionCompletionCounitFromEventFlow
        (hausdorffReflectionCompletionCounitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U V R S W Q D E H C P N =>
      change
        some
          (HausdorffReflectionCompletionCounitUp.mk
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist U))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist V))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist R))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist S))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist W))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist Q))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist D))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist E))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist H))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist C))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist P))
            (hausdorffReflectionCompletionCounitDecodeBHist
              (hausdorffReflectionCompletionCounitEncodeBHist N))) =
          some (HausdorffReflectionCompletionCounitUp.mk U V R S W Q D E H C P N)
      rw [HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode U,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode V,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode R,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode S,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode W,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode Q,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode D,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode E,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode H,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode C,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode P,
        HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode N]

private theorem HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_injective
    {x y : HausdorffReflectionCompletionCounitUp} :
    hausdorffReflectionCompletionCounitToEventFlow x =
      hausdorffReflectionCompletionCounitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffReflectionCompletionCounitFromEventFlow
          (hausdorffReflectionCompletionCounitToEventFlow x) =
        hausdorffReflectionCompletionCounitFromEventFlow
          (hausdorffReflectionCompletionCounitToEventFlow y) :=
    congrArg hausdorffReflectionCompletionCounitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_round_trip y)))

instance hausdorffReflectionCompletionCounitBHistCarrier :
    BHistCarrier HausdorffReflectionCompletionCounitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffReflectionCompletionCounitToEventFlow
  fromEventFlow := hausdorffReflectionCompletionCounitFromEventFlow

instance hausdorffReflectionCompletionCounitChapterTasteGate :
    ChapterTasteGate HausdorffReflectionCompletionCounitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffReflectionCompletionCounitFromEventFlow
        (hausdorffReflectionCompletionCounitToEventFlow x) = some x
    exact HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_injective heq)

theorem HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment :
    (forall h : BHist,
      hausdorffReflectionCompletionCounitDecodeBHist
        (hausdorffReflectionCompletionCounitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HausdorffReflectionCompletionCounitUp) ∧
        Nonempty (ChapterTasteGate HausdorffReflectionCompletionCounitUp) ∧
          hausdorffReflectionCompletionCounitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HausdorffReflectionCompletionCounitTasteGate_single_carrier_alignment_decode_encode,
      ⟨hausdorffReflectionCompletionCounitBHistCarrier⟩,
      ⟨hausdorffReflectionCompletionCounitChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HausdorffReflectionCompletionCounitUp
