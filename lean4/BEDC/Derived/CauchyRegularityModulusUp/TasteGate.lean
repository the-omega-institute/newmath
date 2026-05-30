import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRegularityModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRegularityModulusUp : Type where
  | mk (K U W D R E H C P N : BHist) : CauchyRegularityModulusUp
  deriving DecidableEq

def cauchyRegularityModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRegularityModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRegularityModulusEncodeBHist h

def cauchyRegularityModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRegularityModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRegularityModulusDecodeBHist tail)

private theorem cauchyRegularityModulus_decode_encode :
    ∀ h : BHist,
      cauchyRegularityModulusDecodeBHist
          (cauchyRegularityModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRegularityModulusFields :
    CauchyRegularityModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRegularityModulusUp.mk K U W D R E H C P N =>
      [K, U, W, D, R, E, H, C, P, N]

def cauchyRegularityModulusToEventFlow :
    CauchyRegularityModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyRegularityModulusEncodeBHist
      (cauchyRegularityModulusFields x)

def cauchyRegularityModulusFromEventFlow :
    EventFlow → Option CauchyRegularityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | [] => none
    | K :: restK =>
        match restK with
        | [] => none
        | U :: restU =>
            match restU with
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
                                                  (CauchyRegularityModulusUp.mk
                                                    (cauchyRegularityModulusDecodeBHist K)
                                                    (cauchyRegularityModulusDecodeBHist U)
                                                    (cauchyRegularityModulusDecodeBHist W)
                                                    (cauchyRegularityModulusDecodeBHist D)
                                                    (cauchyRegularityModulusDecodeBHist R)
                                                    (cauchyRegularityModulusDecodeBHist E)
                                                    (cauchyRegularityModulusDecodeBHist H)
                                                    (cauchyRegularityModulusDecodeBHist C)
                                                    (cauchyRegularityModulusDecodeBHist P)
                                                    (cauchyRegularityModulusDecodeBHist N))
                                            | _ :: _ => none

private theorem cauchyRegularityModulus_round_trip :
    ∀ x : CauchyRegularityModulusUp,
      cauchyRegularityModulusFromEventFlow
          (cauchyRegularityModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K U W D R E H C P N =>
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
                          (congr
                            (congrArg CauchyRegularityModulusUp.mk
                              (cauchyRegularityModulus_decode_encode K))
                            (cauchyRegularityModulus_decode_encode U))
                          (cauchyRegularityModulus_decode_encode W))
                        (cauchyRegularityModulus_decode_encode D))
                      (cauchyRegularityModulus_decode_encode R))
                    (cauchyRegularityModulus_decode_encode E))
                  (cauchyRegularityModulus_decode_encode H))
                (cauchyRegularityModulus_decode_encode C))
              (cauchyRegularityModulus_decode_encode P))
            (cauchyRegularityModulus_decode_encode N))

private theorem cauchyRegularityModulusToEventFlow_injective
    {x y : CauchyRegularityModulusUp} :
    cauchyRegularityModulusToEventFlow x =
        cauchyRegularityModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRegularityModulusFromEventFlow (cauchyRegularityModulusToEventFlow x) =
        cauchyRegularityModulusFromEventFlow (cauchyRegularityModulusToEventFlow y) :=
    congrArg cauchyRegularityModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (cauchyRegularityModulus_round_trip x).symm
      (Eq.trans hread (cauchyRegularityModulus_round_trip y)))

instance cauchyRegularityModulusBHistCarrier :
    BHistCarrier CauchyRegularityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRegularityModulusToEventFlow
  fromEventFlow := cauchyRegularityModulusFromEventFlow

instance cauchyRegularityModulusChapterTasteGate :
    ChapterTasteGate CauchyRegularityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    cases x with
    | mk K U W D R E H C P N =>
        exact cauchyRegularityModulus_round_trip
          (CauchyRegularityModulusUp.mk K U W D R E H C P N)
  layer_separation := by
    intro x y hxy heq
    apply hxy
    apply cauchyRegularityModulusToEventFlow_injective
    simpa only [BHistCarrier.toEventFlow] using heq

def taste_gate : ChapterTasteGate CauchyRegularityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRegularityModulusChapterTasteGate

theorem CauchyRegularityModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyRegularityModulusDecodeBHist
          (cauchyRegularityModulusEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CauchyRegularityModulusUp) ∧
        Nonempty (ChapterTasteGate CauchyRegularityModulusUp) ∧
          cauchyRegularityModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyRegularityModulus_decode_encode,
      ⟨cauchyRegularityModulusBHistCarrier⟩,
      ⟨cauchyRegularityModulusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyRegularityModulusUp
