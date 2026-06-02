import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuousImageCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuousImageCompactUp : Type where
  | mk (K F U E T H C P N : BHist) : ContinuousImageCompactUp
  deriving DecidableEq

def continuousImageCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuousImageCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuousImageCompactEncodeBHist h

def continuousImageCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuousImageCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuousImageCompactDecodeBHist tail)

private theorem ContinuousImageCompactTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      continuousImageCompactDecodeBHist
          (continuousImageCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuousImageCompactToEventFlow : ContinuousImageCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousImageCompactUp.mk K F U E T H C P N =>
      [continuousImageCompactEncodeBHist K,
        continuousImageCompactEncodeBHist F,
        continuousImageCompactEncodeBHist U,
        continuousImageCompactEncodeBHist E,
        continuousImageCompactEncodeBHist T,
        continuousImageCompactEncodeBHist H,
        continuousImageCompactEncodeBHist C,
        continuousImageCompactEncodeBHist P,
        continuousImageCompactEncodeBHist N]

def continuousImageCompactFromEventFlow : EventFlow → Option ContinuousImageCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: restF =>
      match restF with
      | [] => none
      | F :: restU =>
          match restU with
          | [] => none
          | U :: restE =>
              match restE with
              | [] => none
              | E :: restT =>
                  match restT with
                  | [] => none
                  | T :: restH =>
                      match restH with
                      | [] => none
                      | H :: restC =>
                          match restC with
                          | [] => none
                          | C :: restP =>
                              match restP with
                              | [] => none
                              | P :: restN =>
                                  match restN with
                                  | [] => none
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (ContinuousImageCompactUp.mk
                                              (continuousImageCompactDecodeBHist K)
                                              (continuousImageCompactDecodeBHist F)
                                              (continuousImageCompactDecodeBHist U)
                                              (continuousImageCompactDecodeBHist E)
                                              (continuousImageCompactDecodeBHist T)
                                              (continuousImageCompactDecodeBHist H)
                                              (continuousImageCompactDecodeBHist C)
                                              (continuousImageCompactDecodeBHist P)
                                              (continuousImageCompactDecodeBHist N))
                                      | _ :: _ => none

private theorem ContinuousImageCompactTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContinuousImageCompactUp,
      continuousImageCompactFromEventFlow
          (continuousImageCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K F U E T H C P N =>
      change
        some
          (ContinuousImageCompactUp.mk
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist K))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist F))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist U))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist E))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist T))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist H))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist C))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist P))
            (continuousImageCompactDecodeBHist (continuousImageCompactEncodeBHist N))) =
          some (ContinuousImageCompactUp.mk K F U E T H C P N)
      rw [ContinuousImageCompactTasteGate_single_carrier_alignment_decode K,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode F,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode U,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode E,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode T,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode H,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode C,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode P,
        ContinuousImageCompactTasteGate_single_carrier_alignment_decode N]

private theorem ContinuousImageCompactToEventFlow_injective
    {x y : ContinuousImageCompactUp} :
    continuousImageCompactToEventFlow x =
        continuousImageCompactToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuousImageCompactFromEventFlow (continuousImageCompactToEventFlow x) =
        continuousImageCompactFromEventFlow (continuousImageCompactToEventFlow y) :=
    congrArg continuousImageCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContinuousImageCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContinuousImageCompactTasteGate_single_carrier_alignment_round_trip y)))

instance continuousImageCompactBHistCarrier : BHistCarrier ContinuousImageCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuousImageCompactToEventFlow
  fromEventFlow := continuousImageCompactFromEventFlow

instance continuousImageCompactChapterTasteGate :
    ChapterTasteGate ContinuousImageCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      continuousImageCompactFromEventFlow
          (continuousImageCompactToEventFlow x) = some x
    exact ContinuousImageCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContinuousImageCompactToEventFlow_injective heq)

theorem ContinuousImageCompactTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        continuousImageCompactDecodeBHist
            (continuousImageCompactEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ContinuousImageCompactUp) ∧
        Nonempty (ChapterTasteGate ContinuousImageCompactUp) ∧
          continuousImageCompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ContinuousImageCompactTasteGate_single_carrier_alignment_decode,
      ⟨continuousImageCompactBHistCarrier⟩,
      ⟨continuousImageCompactChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ContinuousImageCompactUp
