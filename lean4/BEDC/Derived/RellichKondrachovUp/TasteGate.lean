import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RellichKondrachovUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RellichKondrachovUp : Type where
  | mk (D W S E C M T L H P N : BHist) : RellichKondrachovUp
  deriving DecidableEq

def rellichKondrachovEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rellichKondrachovEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rellichKondrachovEncodeBHist h

def rellichKondrachovDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rellichKondrachovDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rellichKondrachovDecodeBHist tail)

private theorem rellichKondrachov_decode_encode_bhist :
    ∀ h : BHist, rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rellichKondrachovFields : RellichKondrachovUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RellichKondrachovUp.mk D W S E C M T L H P N => [D, W, S, E, C, M, T, L, H, P, N]

def rellichKondrachovToEventFlow : RellichKondrachovUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rellichKondrachovFields x).map rellichKondrachovEncodeBHist

def rellichKondrachovFromEventFlow : EventFlow → Option RellichKondrachovUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _D :: [] => none
  | _D :: _W :: [] => none
  | _D :: _W :: _S :: [] => none
  | _D :: _W :: _S :: _E :: [] => none
  | _D :: _W :: _S :: _E :: _C :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: _H :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: _H :: _P :: [] => none
  | D :: W :: S :: E :: C :: M :: T :: L :: H :: P :: N :: [] =>
      some
        (RellichKondrachovUp.mk
          (rellichKondrachovDecodeBHist D)
          (rellichKondrachovDecodeBHist W)
          (rellichKondrachovDecodeBHist S)
          (rellichKondrachovDecodeBHist E)
          (rellichKondrachovDecodeBHist C)
          (rellichKondrachovDecodeBHist M)
          (rellichKondrachovDecodeBHist T)
          (rellichKondrachovDecodeBHist L)
          (rellichKondrachovDecodeBHist H)
          (rellichKondrachovDecodeBHist P)
          (rellichKondrachovDecodeBHist N))
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: _H :: _P :: _N ::
      _extra :: _rest =>
      none

private theorem rellichKondrachov_round_trip :
    ∀ x : RellichKondrachovUp,
      rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W S E C M T L H P N =>
      change
        some
          (RellichKondrachovUp.mk
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist D))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist W))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist S))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist E))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist C))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist M))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist T))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist L))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist H))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist P))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist N))) =
          some (RellichKondrachovUp.mk D W S E C M T L H P N)
      rw [rellichKondrachov_decode_encode_bhist D,
        rellichKondrachov_decode_encode_bhist W,
        rellichKondrachov_decode_encode_bhist S,
        rellichKondrachov_decode_encode_bhist E,
        rellichKondrachov_decode_encode_bhist C,
        rellichKondrachov_decode_encode_bhist M,
        rellichKondrachov_decode_encode_bhist T,
        rellichKondrachov_decode_encode_bhist L,
        rellichKondrachov_decode_encode_bhist H,
        rellichKondrachov_decode_encode_bhist P,
        rellichKondrachov_decode_encode_bhist N]

private theorem rellichKondrachovToEventFlow_injective {x y : RellichKondrachovUp} :
    rellichKondrachovToEventFlow x = rellichKondrachovToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) =
        rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow y) :=
    congrArg rellichKondrachovFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rellichKondrachov_round_trip x).symm
      (Eq.trans hread (rellichKondrachov_round_trip y)))

instance rellichKondrachovBHistCarrier : BHistCarrier RellichKondrachovUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rellichKondrachovToEventFlow
  fromEventFlow := rellichKondrachovFromEventFlow

instance rellichKondrachovChapterTasteGate : ChapterTasteGate RellichKondrachovUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) = some x
    exact rellichKondrachov_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rellichKondrachovToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RellichKondrachovUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rellichKondrachovChapterTasteGate

theorem RellichKondrachovTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RellichKondrachovUp) ∧
      Nonempty (ChapterTasteGate RellichKondrachovUp) ∧
        (∀ h : BHist, rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist h) = h) ∧
          (∀ x : RellichKondrachovUp,
            rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) = some x) ∧
            rellichKondrachovEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro rellichKondrachovBHistCarrier,
      Nonempty.intro rellichKondrachovChapterTasteGate,
      rellichKondrachov_decode_encode_bhist,
      rellichKondrachov_round_trip,
      rfl⟩

end BEDC.Derived.RellichKondrachovUp
