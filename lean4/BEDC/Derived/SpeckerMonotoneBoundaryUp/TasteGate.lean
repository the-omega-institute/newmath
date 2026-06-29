import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpeckerMonotoneBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpeckerMonotoneBoundaryUp : Type where
  | mk (S W D R B L H C P N : BHist) : SpeckerMonotoneBoundaryUp
  deriving DecidableEq

def speckerMonotoneBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: speckerMonotoneBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: speckerMonotoneBoundaryEncodeBHist h

def speckerMonotoneBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (speckerMonotoneBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (speckerMonotoneBoundaryDecodeBHist tail)

private theorem SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def speckerMonotoneBoundaryToEventFlow : SpeckerMonotoneBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SpeckerMonotoneBoundaryUp.mk S W D R B L H C P N =>
      [[BMark.b0],
        speckerMonotoneBoundaryEncodeBHist S,
        [BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        speckerMonotoneBoundaryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        speckerMonotoneBoundaryEncodeBHist N]

def speckerMonotoneBoundaryFromEventFlow :
    EventFlow → Option SpeckerMonotoneBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagS :: restS =>
      match restS with
      | [] => none
      | S :: restWTag =>
          match restWTag with
          | [] => none
          | _tagW :: restW =>
              match restW with
              | [] => none
              | W :: restDTag =>
                  match restDTag with
                  | [] => none
                  | _tagD :: restD =>
                      match restD with
                      | [] => none
                      | D :: restRTag =>
                          match restRTag with
                          | [] => none
                          | _tagR :: restR =>
                              match restR with
                              | [] => none
                              | R :: restBTag =>
                                  match restBTag with
                                  | [] => none
                                  | _tagB :: restB =>
                                      match restB with
                                      | [] => none
                                      | B :: restLTag =>
                                          match restLTag with
                                          | [] => none
                                          | _tagL :: restL =>
                                              match restL with
                                              | [] => none
                                              | L :: restHTag =>
                                                  match restHTag with
                                                  | [] => none
                                                  | _tagH :: restH =>
                                                      match restH with
                                                      | [] => none
                                                      | H :: restCTag =>
                                                          match restCTag with
                                                          | [] => none
                                                          | _tagC :: restC =>
                                                              match restC with
                                                              | [] => none
                                                              | C :: restPTag =>
                                                                  match restPTag with
                                                                  | [] => none
                                                                  | _tagP :: restP =>
                                                                      match restP with
                                                                      | [] => none
                                                                      | P :: restNTag =>
                                                                          match restNTag with
                                                                          | [] => none
                                                                          | _tagN :: restN =>
                                                                              match restN with
                                                                              | [] => none
                                                                              | N :: rest =>
                                                                                  match rest with
                                                                                  | [] =>
                                                                                      some
                                                                                        (SpeckerMonotoneBoundaryUp.mk
                                                                                          (speckerMonotoneBoundaryDecodeBHist S)
                                                                                          (speckerMonotoneBoundaryDecodeBHist W)
                                                                                          (speckerMonotoneBoundaryDecodeBHist D)
                                                                                          (speckerMonotoneBoundaryDecodeBHist R)
                                                                                          (speckerMonotoneBoundaryDecodeBHist B)
                                                                                          (speckerMonotoneBoundaryDecodeBHist L)
                                                                                          (speckerMonotoneBoundaryDecodeBHist H)
                                                                                          (speckerMonotoneBoundaryDecodeBHist C)
                                                                                          (speckerMonotoneBoundaryDecodeBHist P)
                                                                                          (speckerMonotoneBoundaryDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SpeckerMonotoneBoundaryUp,
      speckerMonotoneBoundaryFromEventFlow
        (speckerMonotoneBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D R B L H C P N =>
      change
        some
          (SpeckerMonotoneBoundaryUp.mk
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist S))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist W))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist D))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist R))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist B))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist L))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist H))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist C))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist P))
            (speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist N))) =
          some (SpeckerMonotoneBoundaryUp.mk S W D R B L H C P N)
      rw [SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode S,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode W,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode D,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode R,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode B,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode L,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode H,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode C,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode P,
        SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_injective
    {x y : SpeckerMonotoneBoundaryUp} :
    speckerMonotoneBoundaryToEventFlow x = speckerMonotoneBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      speckerMonotoneBoundaryFromEventFlow (speckerMonotoneBoundaryToEventFlow x) =
        speckerMonotoneBoundaryFromEventFlow (speckerMonotoneBoundaryToEventFlow y) :=
    congrArg speckerMonotoneBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance speckerMonotoneBoundaryBHistCarrier : BHistCarrier SpeckerMonotoneBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := speckerMonotoneBoundaryToEventFlow
  fromEventFlow := speckerMonotoneBoundaryFromEventFlow

instance speckerMonotoneBoundaryChapterTasteGate :
    ChapterTasteGate SpeckerMonotoneBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      speckerMonotoneBoundaryFromEventFlow (speckerMonotoneBoundaryToEventFlow x) = some x
    exact SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SpeckerMonotoneBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  speckerMonotoneBoundaryChapterTasteGate

theorem SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      speckerMonotoneBoundaryDecodeBHist (speckerMonotoneBoundaryEncodeBHist h) = h) ∧
      (∀ x : SpeckerMonotoneBoundaryUp,
        speckerMonotoneBoundaryFromEventFlow
          (speckerMonotoneBoundaryToEventFlow x) = some x) ∧
        (∀ x y : SpeckerMonotoneBoundaryUp,
          speckerMonotoneBoundaryToEventFlow x =
            speckerMonotoneBoundaryToEventFlow y → x = y) ∧
          speckerMonotoneBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_decode
  constructor
  · exact SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact SpeckerMonotoneBoundaryTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.SpeckerMonotoneBoundaryUp
