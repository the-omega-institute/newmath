import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterRegularizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterRegularizationUp : Type where
  | mk (F W D R L H C P N : BHist) : CauchyFilterRegularizationUp
  deriving DecidableEq

def cauchyFilterRegularizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterRegularizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterRegularizationEncodeBHist h

def cauchyFilterRegularizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterRegularizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterRegularizationDecodeBHist tail)

private theorem cauchyFilterRegularization_decode_encode :
    ∀ h : BHist,
      cauchyFilterRegularizationDecodeBHist
          (cauchyFilterRegularizationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterRegularizationFields :
    CauchyFilterRegularizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterRegularizationUp.mk F W D R L H C P N =>
      [F, W, D, R, L, H, C, P, N]

def cauchyFilterRegularizationToEventFlow :
    CauchyFilterRegularizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyFilterRegularizationEncodeBHist
      (cauchyFilterRegularizationFields x)

def cauchyFilterRegularizationFromEventFlow :
    EventFlow → Option CauchyFilterRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | [] => none
    | F :: restF =>
        match restF with
        | [] => none
        | W :: restW =>
            match restW with
            | [] => none
            | D :: restD =>
                match restD with
                | [] => none
                | R :: restR =>
                    match restR with
                    | [] => none
                    | L :: restL =>
                        match restL with
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
                                              (CauchyFilterRegularizationUp.mk
                                                (cauchyFilterRegularizationDecodeBHist F)
                                                (cauchyFilterRegularizationDecodeBHist W)
                                                (cauchyFilterRegularizationDecodeBHist D)
                                                (cauchyFilterRegularizationDecodeBHist R)
                                                (cauchyFilterRegularizationDecodeBHist L)
                                                (cauchyFilterRegularizationDecodeBHist H)
                                                (cauchyFilterRegularizationDecodeBHist C)
                                                (cauchyFilterRegularizationDecodeBHist P)
                                                (cauchyFilterRegularizationDecodeBHist N))
                                        | _ :: _ => none

private theorem cauchyFilterRegularization_round_trip :
    ∀ x : CauchyFilterRegularizationUp,
      cauchyFilterRegularizationFromEventFlow
          (cauchyFilterRegularizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W D R L H C P N =>
      exact
        congrArg (fun z => some z)
          (congr
            (congr
              (congr
                (congr
                  (congr
                    (congr
                      (congr
                        (congr
                          (congrArg CauchyFilterRegularizationUp.mk
                            (cauchyFilterRegularization_decode_encode F))
                          (cauchyFilterRegularization_decode_encode W))
                        (cauchyFilterRegularization_decode_encode D))
                      (cauchyFilterRegularization_decode_encode R))
                    (cauchyFilterRegularization_decode_encode L))
                  (cauchyFilterRegularization_decode_encode H))
                (cauchyFilterRegularization_decode_encode C))
              (cauchyFilterRegularization_decode_encode P))
            (cauchyFilterRegularization_decode_encode N))

private theorem cauchyFilterRegularizationToEventFlow_injective
    {x y : CauchyFilterRegularizationUp} :
    cauchyFilterRegularizationToEventFlow x =
        cauchyFilterRegularizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterRegularizationFromEventFlow
          (cauchyFilterRegularizationToEventFlow x) =
        cauchyFilterRegularizationFromEventFlow
          (cauchyFilterRegularizationToEventFlow y) :=
    congrArg cauchyFilterRegularizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (cauchyFilterRegularization_round_trip x).symm
      (Eq.trans hread (cauchyFilterRegularization_round_trip y)))

instance cauchyFilterRegularizationBHistCarrier :
    BHistCarrier CauchyFilterRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterRegularizationToEventFlow
  fromEventFlow := cauchyFilterRegularizationFromEventFlow

instance cauchyFilterRegularizationChapterTasteGate :
    ChapterTasteGate CauchyFilterRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    cases x with
    | mk F W D R L H C P N =>
        exact cauchyFilterRegularization_round_trip
          (CauchyFilterRegularizationUp.mk F W D R L H C P N)
  layer_separation := by
    intro x y hxy heq
    apply hxy
    apply cauchyFilterRegularizationToEventFlow_injective
    simpa only [BHistCarrier.toEventFlow] using heq

def taste_gate : ChapterTasteGate CauchyFilterRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterRegularizationChapterTasteGate

theorem CauchyFilterRegularizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyFilterRegularizationDecodeBHist
          (cauchyFilterRegularizationEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CauchyFilterRegularizationUp) ∧
        Nonempty (ChapterTasteGate CauchyFilterRegularizationUp) ∧
          cauchyFilterRegularizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyFilterRegularization_decode_encode,
      ⟨cauchyFilterRegularizationBHistCarrier⟩,
      ⟨cauchyFilterRegularizationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyFilterRegularizationUp
