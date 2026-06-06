import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusExtractionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (S R D T E H C P N : BHist) : RegularCauchyModulusExtractionUp
  deriving DecidableEq

def regularCauchyModulusExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusExtractionEncodeBHist h

def regularCauchyModulusExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusExtractionDecodeBHist tail)

private theorem RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyModulusExtractionDecodeBHist
        (regularCauchyModulusExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyModulusExtractionToEventFlow :
    RegularCauchyModulusExtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusExtractionUp.mk S R D T E H C P N =>
      [regularCauchyModulusExtractionEncodeBHist S,
        regularCauchyModulusExtractionEncodeBHist R,
        regularCauchyModulusExtractionEncodeBHist D,
        regularCauchyModulusExtractionEncodeBHist T,
        regularCauchyModulusExtractionEncodeBHist E,
        regularCauchyModulusExtractionEncodeBHist H,
        regularCauchyModulusExtractionEncodeBHist C,
        regularCauchyModulusExtractionEncodeBHist P,
        regularCauchyModulusExtractionEncodeBHist N]

def regularCauchyModulusExtractionFromEventFlow :
    EventFlow → Option RegularCauchyModulusExtractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | R :: restR =>
          match restR with
          | D :: restD =>
              match restD with
              | T :: restT =>
                  match restT with
                  | E :: restE =>
                      match restE with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (RegularCauchyModulusExtractionUp.mk
                                              (regularCauchyModulusExtractionDecodeBHist S)
                                              (regularCauchyModulusExtractionDecodeBHist R)
                                              (regularCauchyModulusExtractionDecodeBHist D)
                                              (regularCauchyModulusExtractionDecodeBHist T)
                                              (regularCauchyModulusExtractionDecodeBHist E)
                                              (regularCauchyModulusExtractionDecodeBHist H)
                                              (regularCauchyModulusExtractionDecodeBHist C)
                                              (regularCauchyModulusExtractionDecodeBHist P)
                                              (regularCauchyModulusExtractionDecodeBHist N))
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

private theorem RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyModulusExtractionUp,
      regularCauchyModulusExtractionFromEventFlow
        (regularCauchyModulusExtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D T E H C P N =>
      change
        some
          (RegularCauchyModulusExtractionUp.mk
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist S))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist R))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist D))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist T))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist E))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist H))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist C))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist P))
            (regularCauchyModulusExtractionDecodeBHist
              (regularCauchyModulusExtractionEncodeBHist N))) =
          some (RegularCauchyModulusExtractionUp.mk S R D T E H C P N)
      rw [RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode S,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode R,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode D,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode T,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode E,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode H,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode C,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode P,
        RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyModulusExtractionUp} :
    regularCauchyModulusExtractionToEventFlow x =
      regularCauchyModulusExtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyModulusExtractionFromEventFlow
          (regularCauchyModulusExtractionToEventFlow x) =
        regularCauchyModulusExtractionFromEventFlow
          (regularCauchyModulusExtractionToEventFlow y) :=
    congrArg regularCauchyModulusExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyModulusExtractionBHistCarrier :
    BHistCarrier RegularCauchyModulusExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusExtractionToEventFlow
  fromEventFlow := regularCauchyModulusExtractionFromEventFlow

instance regularCauchyModulusExtractionChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusExtractionFromEventFlow
        (regularCauchyModulusExtractionToEventFlow x) = some x
    exact RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyModulusExtractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyModulusExtractionDecodeBHist
        (regularCauchyModulusExtractionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyModulusExtractionUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyModulusExtractionUp) ∧
          regularCauchyModulusExtractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyModulusExtractionTasteGate_single_carrier_alignment_decode,
      ⟨regularCauchyModulusExtractionBHistCarrier⟩,
      ⟨regularCauchyModulusExtractionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyModulusExtractionUp
