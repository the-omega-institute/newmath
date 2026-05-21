import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StationaryRationalCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StationaryRationalCauchyUp : Type where
  | mk (q A R D E P N : BHist) : StationaryRationalCauchyUp
  deriving DecidableEq

def stationaryRationalCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stationaryRationalCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stationaryRationalCauchyEncodeBHist h

def stationaryRationalCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stationaryRationalCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stationaryRationalCauchyDecodeBHist tail)

private theorem stationaryRationalCauchy_decode_encode :
    ∀ h : BHist,
      stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stationaryRationalCauchyFields : StationaryRationalCauchyUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | StationaryRationalCauchyUp.mk q A R D E P N => [q, A, R, D, E, P, N]

def stationaryRationalCauchyToEventFlow :
    StationaryRationalCauchyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | StationaryRationalCauchyUp.mk q A R D E P N =>
      [stationaryRationalCauchyEncodeBHist q,
        stationaryRationalCauchyEncodeBHist A,
        stationaryRationalCauchyEncodeBHist R,
        stationaryRationalCauchyEncodeBHist D,
        stationaryRationalCauchyEncodeBHist E,
        stationaryRationalCauchyEncodeBHist P,
        stationaryRationalCauchyEncodeBHist N]

def stationaryRationalCauchyFromEventFlow :
    EventFlow → Option StationaryRationalCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | _q :: [] => none
  | _q :: _A :: [] => none
  | _q :: _A :: _R :: [] => none
  | _q :: _A :: _R :: _D :: [] => none
  | _q :: _A :: _R :: _D :: _E :: [] => none
  | _q :: _A :: _R :: _D :: _E :: _P :: [] => none
  | q :: A :: R :: D :: E :: P :: N :: [] =>
      some
        (StationaryRationalCauchyUp.mk
          (stationaryRationalCauchyDecodeBHist q)
          (stationaryRationalCauchyDecodeBHist A)
          (stationaryRationalCauchyDecodeBHist R)
          (stationaryRationalCauchyDecodeBHist D)
          (stationaryRationalCauchyDecodeBHist E)
          (stationaryRationalCauchyDecodeBHist P)
          (stationaryRationalCauchyDecodeBHist N))
  | _q :: _A :: _R :: _D :: _E :: _P :: _N :: _extra :: _rest => none

private theorem stationaryRationalCauchy_round_trip :
    ∀ x : StationaryRationalCauchyUp,
      stationaryRationalCauchyFromEventFlow (stationaryRationalCauchyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q A R D E P N =>
      exact
        Eq.trans
          (congrArg
            (fun z =>
              some
                (StationaryRationalCauchyUp.mk z
                  (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist A))
                  (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist R))
                  (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist D))
                  (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist E))
                  (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist P))
                  (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist N))))
            (stationaryRationalCauchy_decode_encode q))
          (Eq.trans
            (congrArg
              (fun z =>
                some
                  (StationaryRationalCauchyUp.mk q z
                    (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist R))
                    (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist D))
                    (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist E))
                    (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist P))
                    (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist N))))
              (stationaryRationalCauchy_decode_encode A))
            (Eq.trans
              (congrArg
                (fun z =>
                  some
                    (StationaryRationalCauchyUp.mk q A z
                      (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist D))
                      (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist E))
                      (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist P))
                      (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist N))))
                (stationaryRationalCauchy_decode_encode R))
              (Eq.trans
                (congrArg
                  (fun z =>
                    some
                      (StationaryRationalCauchyUp.mk q A R z
                        (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist E))
                        (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist P))
                        (stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist N))))
                  (stationaryRationalCauchy_decode_encode D))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      some
                        (StationaryRationalCauchyUp.mk q A R D z
                          (stationaryRationalCauchyDecodeBHist
                            (stationaryRationalCauchyEncodeBHist P))
                          (stationaryRationalCauchyDecodeBHist
                            (stationaryRationalCauchyEncodeBHist N))))
                    (stationaryRationalCauchy_decode_encode E))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        some
                          (StationaryRationalCauchyUp.mk q A R D E z
                            (stationaryRationalCauchyDecodeBHist
                              (stationaryRationalCauchyEncodeBHist N))))
                      (stationaryRationalCauchy_decode_encode P))
                    (congrArg
                      (fun z => some (StationaryRationalCauchyUp.mk q A R D E P z))
                      (stationaryRationalCauchy_decode_encode N)))))))

private theorem stationaryRationalCauchyEncodeBHist_injective {a b : BHist} :
    stationaryRationalCauchyEncodeBHist a = stationaryRationalCauchyEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  exact Eq.trans (stationaryRationalCauchy_decode_encode a).symm
    (Eq.trans (congrArg stationaryRationalCauchyDecodeBHist h)
      (stationaryRationalCauchy_decode_encode b))

private theorem stationaryRationalCauchyToEventFlow_injective
    {x y : StationaryRationalCauchyUp} :
    stationaryRationalCauchyToEventFlow x = stationaryRationalCauchyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hx :
      stationaryRationalCauchyFromEventFlow (stationaryRationalCauchyToEventFlow x) =
        some x :=
    stationaryRationalCauchy_round_trip x
  have hy :
      stationaryRationalCauchyFromEventFlow (stationaryRationalCauchyToEventFlow y) =
        some y :=
    stationaryRationalCauchy_round_trip y
  have hflow :
      stationaryRationalCauchyFromEventFlow (stationaryRationalCauchyToEventFlow x) =
        stationaryRationalCauchyFromEventFlow (stationaryRationalCauchyToEventFlow y) :=
    congrArg stationaryRationalCauchyFromEventFlow hxy
  have hsome : some x = some y := Eq.trans hx.symm (Eq.trans hflow hy)
  cases hsome
  rfl

private theorem stationaryRationalCauchy_field_faithful :
    ∀ x y : StationaryRationalCauchyUp,
      stationaryRationalCauchyFields x = stationaryRationalCauchyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk q1 A1 R1 D1 E1 P1 N1 =>
      cases y with
      | mk q2 A2 R2 D2 E2 P2 N2 =>
          cases h
          rfl

instance stationaryRationalCauchyBHistCarrier :
    BHistCarrier StationaryRationalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stationaryRationalCauchyToEventFlow
  fromEventFlow := stationaryRationalCauchyFromEventFlow

instance stationaryRationalCauchyChapterTasteGate :
    ChapterTasteGate StationaryRationalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stationaryRationalCauchyFromEventFlow (stationaryRationalCauchyToEventFlow x) =
        some x
    exact stationaryRationalCauchy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stationaryRationalCauchyToEventFlow_injective heq)

instance stationaryRationalCauchyFieldFaithful :
    FieldFaithful StationaryRationalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stationaryRationalCauchyFields
  field_faithful := stationaryRationalCauchy_field_faithful

instance stationaryRationalCauchyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial StationaryRationalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StationaryRationalCauchyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      StationaryRationalCauchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StationaryRationalCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stationaryRationalCauchyChapterTasteGate

theorem StationaryRationalCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      stationaryRationalCauchyDecodeBHist (stationaryRationalCauchyEncodeBHist h) = h) ∧
      (∀ x : StationaryRationalCauchyUp,
        stationaryRationalCauchyFromEventFlow (stationaryRationalCauchyToEventFlow x) =
          some x) ∧
      (∀ x y : StationaryRationalCauchyUp,
        stationaryRationalCauchyToEventFlow x = stationaryRationalCauchyToEventFlow y →
          x = y) ∧
      stationaryRationalCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨stationaryRationalCauchy_decode_encode,
      stationaryRationalCauchy_round_trip,
      fun x y hxy => stationaryRationalCauchyToEventFlow_injective hxy,
      rfl⟩

theorem StationaryRationalCauchyUpTasteGate_single_carrier_alignment_ChapterTasteGate :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier StationaryRationalCauchyUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate StationaryRationalCauchyUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨stationaryRationalCauchyBHistCarrier⟩,
      ⟨stationaryRationalCauchyChapterTasteGate⟩⟩

end BEDC.Derived.StationaryRationalCauchyUp
