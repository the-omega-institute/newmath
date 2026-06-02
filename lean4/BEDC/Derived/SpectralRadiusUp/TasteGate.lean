import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpectralRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpectralRadiusUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (A a W Q G E H C P N : BHist) : SpectralRadiusUp
  deriving DecidableEq

def spectralRadiusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: spectralRadiusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: spectralRadiusEncodeBHist h

def spectralRadiusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (spectralRadiusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (spectralRadiusDecodeBHist tail)

private theorem spectralRadius_decode_encode_bhist :
    ∀ h : BHist, spectralRadiusDecodeBHist (spectralRadiusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def spectralRadiusFields : SpectralRadiusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpectralRadiusUp.mk A a W Q G E H C P N => [A, a, W, Q, G, E, H, C, P, N]

def spectralRadiusToEventFlow : SpectralRadiusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (spectralRadiusFields x).map spectralRadiusEncodeBHist

def spectralRadiusFromEventFlow : EventFlow → Option SpectralRadiusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _A :: [] => none
  | _A :: _a :: [] => none
  | _A :: _a :: _W :: [] => none
  | _A :: _a :: _W :: _Q :: [] => none
  | _A :: _a :: _W :: _Q :: _G :: [] => none
  | _A :: _a :: _W :: _Q :: _G :: _E :: [] => none
  | _A :: _a :: _W :: _Q :: _G :: _E :: _H :: [] => none
  | _A :: _a :: _W :: _Q :: _G :: _E :: _H :: _C :: [] => none
  | _A :: _a :: _W :: _Q :: _G :: _E :: _H :: _C :: _P :: [] => none
  | A :: a :: W :: Q :: G :: E :: H :: C :: P :: N :: [] =>
      some
        (SpectralRadiusUp.mk
          (spectralRadiusDecodeBHist A)
          (spectralRadiusDecodeBHist a)
          (spectralRadiusDecodeBHist W)
          (spectralRadiusDecodeBHist Q)
          (spectralRadiusDecodeBHist G)
          (spectralRadiusDecodeBHist E)
          (spectralRadiusDecodeBHist H)
          (spectralRadiusDecodeBHist C)
          (spectralRadiusDecodeBHist P)
          (spectralRadiusDecodeBHist N))
  | _A :: _a :: _W :: _Q :: _G :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem spectralRadius_round_trip :
    ∀ x : SpectralRadiusUp, spectralRadiusFromEventFlow (spectralRadiusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A a W Q G E H C P N =>
      change
        some
          (SpectralRadiusUp.mk
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist A))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist a))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist W))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist Q))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist G))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist E))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist H))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist C))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist P))
            (spectralRadiusDecodeBHist (spectralRadiusEncodeBHist N))) =
          some (SpectralRadiusUp.mk A a W Q G E H C P N)
      rw [spectralRadius_decode_encode_bhist A,
        spectralRadius_decode_encode_bhist a,
        spectralRadius_decode_encode_bhist W,
        spectralRadius_decode_encode_bhist Q,
        spectralRadius_decode_encode_bhist G,
        spectralRadius_decode_encode_bhist E,
        spectralRadius_decode_encode_bhist H,
        spectralRadius_decode_encode_bhist C,
        spectralRadius_decode_encode_bhist P,
        spectralRadius_decode_encode_bhist N]

private theorem spectralRadiusToEventFlow_injective {x y : SpectralRadiusUp} :
    spectralRadiusToEventFlow x = spectralRadiusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      spectralRadiusFromEventFlow (spectralRadiusToEventFlow x) =
        spectralRadiusFromEventFlow (spectralRadiusToEventFlow y) :=
    congrArg spectralRadiusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (spectralRadius_round_trip x).symm
      (Eq.trans hread (spectralRadius_round_trip y)))

instance spectralRadiusBHistCarrier : BHistCarrier SpectralRadiusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := spectralRadiusToEventFlow
  fromEventFlow := spectralRadiusFromEventFlow

instance spectralRadiusChapterTasteGate : ChapterTasteGate SpectralRadiusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change spectralRadiusFromEventFlow (spectralRadiusToEventFlow x) = some x
    exact spectralRadius_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (spectralRadiusToEventFlow_injective heq)

theorem SpectralRadiusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SpectralRadiusUp) ∧ Nonempty (ChapterTasteGate SpectralRadiusUp) ∧
      (∀ h : BHist,
        spectralRadiusDecodeBHist (BMark.b0 :: spectralRadiusEncodeBHist h) = BHist.e0 h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨spectralRadiusBHistCarrier⟩, ⟨spectralRadiusChapterTasteGate⟩,
      fun h => congrArg BHist.e0 (spectralRadius_decode_encode_bhist h)⟩

end BEDC.Derived.SpectralRadiusUp
