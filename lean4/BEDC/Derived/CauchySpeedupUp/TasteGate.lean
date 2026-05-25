import BEDC.Derived.CauchySpeedupUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySpeedupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchySpeedupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySpeedupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySpeedupEncodeBHist h

def cauchySpeedupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySpeedupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySpeedupDecodeBHist tail)

theorem CauchySpeedupTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySpeedupFields : BEDC.Derived.CauchySpeedupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchySpeedupUp.mk A J D W R E H C P N => [A, J, D, W, R, E, H, C, P, N]

def cauchySpeedupToEventFlow : BEDC.Derived.CauchySpeedupUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySpeedupFields x).map cauchySpeedupEncodeBHist

def cauchySpeedupFromEventFlow :
    EventFlow → Option BEDC.Derived.CauchySpeedupUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _A :: [] => none
  | _A :: _J :: [] => none
  | _A :: _J :: _D :: [] => none
  | _A :: _J :: _D :: _W :: [] => none
  | _A :: _J :: _D :: _W :: _R :: [] => none
  | _A :: _J :: _D :: _W :: _R :: _E :: [] => none
  | _A :: _J :: _D :: _W :: _R :: _E :: _H :: [] => none
  | _A :: _J :: _D :: _W :: _R :: _E :: _H :: _C :: [] => none
  | _A :: _J :: _D :: _W :: _R :: _E :: _H :: _C :: _P :: [] => none
  | A :: J :: D :: W :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (BEDC.Derived.CauchySpeedupUp.mk
          (cauchySpeedupDecodeBHist A)
          (cauchySpeedupDecodeBHist J)
          (cauchySpeedupDecodeBHist D)
          (cauchySpeedupDecodeBHist W)
          (cauchySpeedupDecodeBHist R)
          (cauchySpeedupDecodeBHist E)
          (cauchySpeedupDecodeBHist H)
          (cauchySpeedupDecodeBHist C)
          (cauchySpeedupDecodeBHist P)
          (cauchySpeedupDecodeBHist N))
  | _A :: _J :: _D :: _W :: _R :: _E :: _H :: _C :: _P :: _N :: _extra => none

private theorem cauchySpeedup_mk_congr
    {A A' J J' D D' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hA : A' = A) (hJ : J' = J) (hD : D' = D) (hW : W' = W)
    (hR : R' = R) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    BEDC.Derived.CauchySpeedupUp.mk A' J' D' W' R' E' H' C' P' N' =
      BEDC.Derived.CauchySpeedupUp.mk A J D W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hJ
  cases hD
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem cauchySpeedup_round_trip :
    ∀ x : BEDC.Derived.CauchySpeedupUp,
      cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  exact
    BEDC.Derived.CauchySpeedupUp.rec
      (motive := fun x =>
        cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x)
      (fun A J D W R E H C P N =>
        congrArg some
          (cauchySpeedup_mk_congr
            (CauchySpeedupTasteGate_single_carrier_alignment_decode A)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode J)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode D)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode W)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode R)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode E)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode H)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode C)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode P)
            (CauchySpeedupTasteGate_single_carrier_alignment_decode N)))
      x

private theorem cauchySpeedupToEventFlow_injective
    {x y : BEDC.Derived.CauchySpeedupUp} :
    cauchySpeedupToEventFlow x = cauchySpeedupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) =
        cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow y) :=
    congrArg cauchySpeedupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySpeedup_round_trip x).symm
      (Eq.trans hread (cauchySpeedup_round_trip y)))

instance cauchySpeedupBHistCarrier :
    BHistCarrier BEDC.Derived.CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySpeedupToEventFlow
  fromEventFlow := cauchySpeedupFromEventFlow

instance cauchySpeedupChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x
    exact cauchySpeedup_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySpeedupToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BEDC.Derived.CauchySpeedupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySpeedupChapterTasteGate

theorem CauchySpeedupTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist h) = h) ∧
      cauchySpeedupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchySpeedupTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.CauchySpeedupUp
