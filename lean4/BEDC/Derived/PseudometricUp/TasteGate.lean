import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PseudometricUp : Type where
  | mk (X M D S R E Z H C N : BHist) : PseudometricUp
  deriving DecidableEq

def pseudometricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pseudometricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pseudometricEncodeBHist h

def pseudometricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pseudometricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pseudometricDecodeBHist tail)

private theorem pseudometric_decode_encode_bhist :
    ∀ h : BHist, pseudometricDecodeBHist (pseudometricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pseudometricFields : PseudometricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PseudometricUp.mk X M D S R E Z H C N => [X, M, D, S, R, E, Z, H, C, N]

def pseudometricToEventFlow : PseudometricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (pseudometricFields x).map pseudometricEncodeBHist

def pseudometricFromEventFlow : EventFlow → Option PseudometricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _M :: [] => none
  | _X :: _M :: _D :: [] => none
  | _X :: _M :: _D :: _S :: [] => none
  | _X :: _M :: _D :: _S :: _R :: [] => none
  | _X :: _M :: _D :: _S :: _R :: _E :: [] => none
  | _X :: _M :: _D :: _S :: _R :: _E :: _Z :: [] => none
  | _X :: _M :: _D :: _S :: _R :: _E :: _Z :: _H :: [] => none
  | _X :: _M :: _D :: _S :: _R :: _E :: _Z :: _H :: _C :: [] => none
  | X :: M :: D :: S :: R :: E :: Z :: H :: C :: N :: [] =>
      some
        (PseudometricUp.mk
          (pseudometricDecodeBHist X)
          (pseudometricDecodeBHist M)
          (pseudometricDecodeBHist D)
          (pseudometricDecodeBHist S)
          (pseudometricDecodeBHist R)
          (pseudometricDecodeBHist E)
          (pseudometricDecodeBHist Z)
          (pseudometricDecodeBHist H)
          (pseudometricDecodeBHist C)
          (pseudometricDecodeBHist N))
  | _X :: _M :: _D :: _S :: _R :: _E :: _Z :: _H :: _C :: _N :: _extra :: _rest =>
      none

private theorem pseudometric_round_trip :
    ∀ x : PseudometricUp, pseudometricFromEventFlow (pseudometricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M D S R E Z H C N =>
      change
        some
          (PseudometricUp.mk
            (pseudometricDecodeBHist (pseudometricEncodeBHist X))
            (pseudometricDecodeBHist (pseudometricEncodeBHist M))
            (pseudometricDecodeBHist (pseudometricEncodeBHist D))
            (pseudometricDecodeBHist (pseudometricEncodeBHist S))
            (pseudometricDecodeBHist (pseudometricEncodeBHist R))
            (pseudometricDecodeBHist (pseudometricEncodeBHist E))
            (pseudometricDecodeBHist (pseudometricEncodeBHist Z))
            (pseudometricDecodeBHist (pseudometricEncodeBHist H))
            (pseudometricDecodeBHist (pseudometricEncodeBHist C))
            (pseudometricDecodeBHist (pseudometricEncodeBHist N))) =
          some (PseudometricUp.mk X M D S R E Z H C N)
      rw [pseudometric_decode_encode_bhist X,
        pseudometric_decode_encode_bhist M,
        pseudometric_decode_encode_bhist D,
        pseudometric_decode_encode_bhist S,
        pseudometric_decode_encode_bhist R,
        pseudometric_decode_encode_bhist E,
        pseudometric_decode_encode_bhist Z,
        pseudometric_decode_encode_bhist H,
        pseudometric_decode_encode_bhist C,
        pseudometric_decode_encode_bhist N]

private theorem pseudometricToEventFlow_injective {x y : PseudometricUp} :
    pseudometricToEventFlow x = pseudometricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pseudometricFromEventFlow (pseudometricToEventFlow x) =
        pseudometricFromEventFlow (pseudometricToEventFlow y) :=
    congrArg pseudometricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (pseudometric_round_trip x).symm
      (Eq.trans hread (pseudometric_round_trip y)))

instance pseudometricBHistCarrier : BHistCarrier PseudometricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pseudometricToEventFlow
  fromEventFlow := pseudometricFromEventFlow

instance pseudometricChapterTasteGate : ChapterTasteGate PseudometricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pseudometricFromEventFlow (pseudometricToEventFlow x) = some x
    exact pseudometric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pseudometricToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PseudometricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pseudometricChapterTasteGate

theorem PseudometricTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PseudometricUp) ∧ Nonempty (ChapterTasteGate PseudometricUp) ∧
      (∀ h : BHist, pseudometricDecodeBHist (pseudometricEncodeBHist h) = h) ∧
      pseudometricEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro pseudometricBHistCarrier,
      Nonempty.intro pseudometricChapterTasteGate,
      pseudometric_decode_encode_bhist,
      rfl⟩

end BEDC.Derived.PseudometricUp
