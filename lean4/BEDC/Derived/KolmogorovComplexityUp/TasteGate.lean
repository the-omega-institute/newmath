import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KolmogorovComplexityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KolmogorovComplexityUp : Type where
  | mk (p U I O F L B E T C P N : BHist) : KolmogorovComplexityUp
  deriving DecidableEq

def kolmogorovComplexityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kolmogorovComplexityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kolmogorovComplexityEncodeBHist h

def kolmogorovComplexityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kolmogorovComplexityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kolmogorovComplexityDecodeBHist tail)

private theorem KolmogorovComplexityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kolmogorovComplexityToEventFlow : KolmogorovComplexityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KolmogorovComplexityUp.mk p U I O F L B E T C P N =>
      [kolmogorovComplexityEncodeBHist p,
        kolmogorovComplexityEncodeBHist U,
        kolmogorovComplexityEncodeBHist I,
        kolmogorovComplexityEncodeBHist O,
        kolmogorovComplexityEncodeBHist F,
        kolmogorovComplexityEncodeBHist L,
        kolmogorovComplexityEncodeBHist B,
        kolmogorovComplexityEncodeBHist E,
        kolmogorovComplexityEncodeBHist T,
        kolmogorovComplexityEncodeBHist C,
        kolmogorovComplexityEncodeBHist P,
        kolmogorovComplexityEncodeBHist N]

def kolmogorovComplexityFromEventFlow : EventFlow → Option KolmogorovComplexityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | p :: restU =>
      match restU with
      | [] => none
      | U :: restI =>
          match restI with
          | [] => none
          | I :: restO =>
              match restO with
              | [] => none
              | O :: restF =>
                  match restF with
                  | [] => none
                  | F :: restL =>
                      match restL with
                      | [] => none
                      | L :: restB =>
                          match restB with
                          | [] => none
                          | B :: restE =>
                              match restE with
                              | [] => none
                              | E :: restT =>
                                  match restT with
                                  | [] => none
                                  | T :: restC =>
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
                                                        (KolmogorovComplexityUp.mk
                                                          (kolmogorovComplexityDecodeBHist p)
                                                          (kolmogorovComplexityDecodeBHist U)
                                                          (kolmogorovComplexityDecodeBHist I)
                                                          (kolmogorovComplexityDecodeBHist O)
                                                          (kolmogorovComplexityDecodeBHist F)
                                                          (kolmogorovComplexityDecodeBHist L)
                                                          (kolmogorovComplexityDecodeBHist B)
                                                          (kolmogorovComplexityDecodeBHist E)
                                                          (kolmogorovComplexityDecodeBHist T)
                                                          (kolmogorovComplexityDecodeBHist C)
                                                          (kolmogorovComplexityDecodeBHist P)
                                                          (kolmogorovComplexityDecodeBHist N))
                                                  | _ :: _ => none

private theorem KolmogorovComplexityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KolmogorovComplexityUp,
      kolmogorovComplexityFromEventFlow (kolmogorovComplexityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk p U I O F L B E T C P N =>
      change
        some
          (KolmogorovComplexityUp.mk
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist p))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist U))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist I))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist O))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist F))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist L))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist B))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist E))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist T))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist C))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist P))
            (kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist N))) =
          some (KolmogorovComplexityUp.mk p U I O F L B E T C P N)
      rw [KolmogorovComplexityTasteGate_single_carrier_alignment_decode p,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode U,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode I,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode O,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode F,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode L,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode B,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode E,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode T,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode C,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode P,
        KolmogorovComplexityTasteGate_single_carrier_alignment_decode N]

private theorem KolmogorovComplexityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KolmogorovComplexityUp} :
    kolmogorovComplexityToEventFlow x = kolmogorovComplexityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kolmogorovComplexityFromEventFlow (kolmogorovComplexityToEventFlow x) =
        kolmogorovComplexityFromEventFlow (kolmogorovComplexityToEventFlow y) :=
    congrArg kolmogorovComplexityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KolmogorovComplexityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KolmogorovComplexityTasteGate_single_carrier_alignment_round_trip y)))

instance kolmogorovComplexityBHistCarrier : BHistCarrier KolmogorovComplexityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kolmogorovComplexityToEventFlow
  fromEventFlow := kolmogorovComplexityFromEventFlow

instance kolmogorovComplexityChapterTasteGate : ChapterTasteGate KolmogorovComplexityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kolmogorovComplexityFromEventFlow (kolmogorovComplexityToEventFlow x) = some x
    exact KolmogorovComplexityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KolmogorovComplexityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem KolmogorovComplexityTasteGate_single_carrier_alignment :
    (∀ h : BHist, kolmogorovComplexityDecodeBHist (kolmogorovComplexityEncodeBHist h) = h) ∧
      (∀ x : KolmogorovComplexityUp,
        kolmogorovComplexityFromEventFlow (kolmogorovComplexityToEventFlow x) = some x) ∧
        (∀ x y : KolmogorovComplexityUp,
          kolmogorovComplexityToEventFlow x = kolmogorovComplexityToEventFlow y → x = y) ∧
          kolmogorovComplexityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KolmogorovComplexityTasteGate_single_carrier_alignment_decode,
      KolmogorovComplexityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KolmogorovComplexityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KolmogorovComplexityUp
