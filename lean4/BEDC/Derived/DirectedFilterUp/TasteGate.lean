import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirectedFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirectedFilterUp : Type where
  | mk (D B M U W R Y E H C P N : BHist) : DirectedFilterUp
  deriving DecidableEq

def directedFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: directedFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: directedFilterEncodeBHist h

def directedFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (directedFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (directedFilterDecodeBHist tail)

private theorem DirectedFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, directedFilterDecodeBHist (directedFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def directedFilterFields : DirectedFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirectedFilterUp.mk D B M U W R Y E H C P N => [D, B, M, U, W, R, Y, E, H, C, P, N]

def directedFilterToEventFlow : DirectedFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DirectedFilterUp.mk D B M U W R Y E H C P N =>
      [directedFilterEncodeBHist D,
        directedFilterEncodeBHist B,
        directedFilterEncodeBHist M,
        directedFilterEncodeBHist U,
        directedFilterEncodeBHist W,
        directedFilterEncodeBHist R,
        directedFilterEncodeBHist Y,
        directedFilterEncodeBHist E,
        directedFilterEncodeBHist H,
        directedFilterEncodeBHist C,
        directedFilterEncodeBHist P,
        directedFilterEncodeBHist N]

def directedFilterFromEventFlow : EventFlow → Option DirectedFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: restB =>
      match restB with
      | [] => none
      | B :: restM =>
          match restM with
          | [] => none
          | M :: restU =>
              match restU with
              | [] => none
              | U :: restW =>
                  match restW with
                  | [] => none
                  | W :: restR =>
                      match restR with
                      | [] => none
                      | R :: restY =>
                          match restY with
                          | [] => none
                          | Y :: restE =>
                              match restE with
                              | [] => none
                              | E :: restH =>
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
                                                        (DirectedFilterUp.mk
                                                          (directedFilterDecodeBHist D)
                                                          (directedFilterDecodeBHist B)
                                                          (directedFilterDecodeBHist M)
                                                          (directedFilterDecodeBHist U)
                                                          (directedFilterDecodeBHist W)
                                                          (directedFilterDecodeBHist R)
                                                          (directedFilterDecodeBHist Y)
                                                          (directedFilterDecodeBHist E)
                                                          (directedFilterDecodeBHist H)
                                                          (directedFilterDecodeBHist C)
                                                          (directedFilterDecodeBHist P)
                                                          (directedFilterDecodeBHist N))
                                                  | _ :: _ => none

private theorem DirectedFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DirectedFilterUp,
      directedFilterFromEventFlow (directedFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk D B M U W R Y E H C P N =>
      change
        some
          (DirectedFilterUp.mk
            (directedFilterDecodeBHist (directedFilterEncodeBHist D))
            (directedFilterDecodeBHist (directedFilterEncodeBHist B))
            (directedFilterDecodeBHist (directedFilterEncodeBHist M))
            (directedFilterDecodeBHist (directedFilterEncodeBHist U))
            (directedFilterDecodeBHist (directedFilterEncodeBHist W))
            (directedFilterDecodeBHist (directedFilterEncodeBHist R))
            (directedFilterDecodeBHist (directedFilterEncodeBHist Y))
            (directedFilterDecodeBHist (directedFilterEncodeBHist E))
            (directedFilterDecodeBHist (directedFilterEncodeBHist H))
            (directedFilterDecodeBHist (directedFilterEncodeBHist C))
            (directedFilterDecodeBHist (directedFilterEncodeBHist P))
            (directedFilterDecodeBHist (directedFilterEncodeBHist N))) =
          some (DirectedFilterUp.mk D B M U W R Y E H C P N)
      rw [DirectedFilterTasteGate_single_carrier_alignment_decode D,
        DirectedFilterTasteGate_single_carrier_alignment_decode B,
        DirectedFilterTasteGate_single_carrier_alignment_decode M,
        DirectedFilterTasteGate_single_carrier_alignment_decode U,
        DirectedFilterTasteGate_single_carrier_alignment_decode W,
        DirectedFilterTasteGate_single_carrier_alignment_decode R,
        DirectedFilterTasteGate_single_carrier_alignment_decode Y,
        DirectedFilterTasteGate_single_carrier_alignment_decode E,
        DirectedFilterTasteGate_single_carrier_alignment_decode H,
        DirectedFilterTasteGate_single_carrier_alignment_decode C,
        DirectedFilterTasteGate_single_carrier_alignment_decode P,
        DirectedFilterTasteGate_single_carrier_alignment_decode N]

private theorem DirectedFilterToEventFlow_injective {x y : DirectedFilterUp} :
    directedFilterToEventFlow x = directedFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      directedFilterFromEventFlow (directedFilterToEventFlow x) =
        directedFilterFromEventFlow (directedFilterToEventFlow y) :=
    congrArg directedFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DirectedFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DirectedFilterTasteGate_single_carrier_alignment_round_trip y)))

instance directedFilterBHistCarrier : BHistCarrier DirectedFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := directedFilterToEventFlow
  fromEventFlow := directedFilterFromEventFlow

instance directedFilterChapterTasteGate : ChapterTasteGate DirectedFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change directedFilterFromEventFlow (directedFilterToEventFlow x) = some x
    exact DirectedFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DirectedFilterToEventFlow_injective heq)

theorem DirectedFilterTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DirectedFilterUp) ∧
      Nonempty (ChapterTasteGate DirectedFilterUp) ∧
        (∀ x : DirectedFilterUp,
          directedFilterFromEventFlow (directedFilterToEventFlow x) = some x) ∧
          directedFilterEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨directedFilterBHistCarrier⟩,
      ⟨directedFilterChapterTasteGate⟩,
      DirectedFilterTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.DirectedFilterUp
