import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeminormedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeminormedSpaceUp : Type where
  | mk : (S N A M T C P L H R : BHist) → SeminormedSpaceUp
  deriving DecidableEq

def seminormedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: seminormedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: seminormedSpaceEncodeBHist h

def seminormedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (seminormedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (seminormedSpaceDecodeBHist tail)

private theorem seminormedSpace_decode_encode_bhist :
    ∀ h : BHist, seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def seminormedSpaceFields : SeminormedSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeminormedSpaceUp.mk S N A M T C P L H R => [S, N, A, M, T, C, P, L, H, R]

def seminormedSpaceToEventFlow : SeminormedSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map seminormedSpaceEncodeBHist (seminormedSpaceFields x)

def seminormedSpaceFromEventFlow : EventFlow → Option SeminormedSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: N :: A :: M :: T :: C :: P :: L :: H :: R :: [] =>
      some
        (SeminormedSpaceUp.mk
          (seminormedSpaceDecodeBHist S)
          (seminormedSpaceDecodeBHist N)
          (seminormedSpaceDecodeBHist A)
          (seminormedSpaceDecodeBHist M)
          (seminormedSpaceDecodeBHist T)
          (seminormedSpaceDecodeBHist C)
          (seminormedSpaceDecodeBHist P)
          (seminormedSpaceDecodeBHist L)
          (seminormedSpaceDecodeBHist H)
          (seminormedSpaceDecodeBHist R))
  | _ => none

private theorem seminormedSpace_round_trip :
    ∀ x : SeminormedSpaceUp,
      seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S N A M T C P L H R =>
      change
        some
          (SeminormedSpaceUp.mk
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist S))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist N))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist A))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist M))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist T))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist C))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist P))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist L))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist H))
            (seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist R))) =
          some (SeminormedSpaceUp.mk S N A M T C P L H R)
      rw [seminormedSpace_decode_encode_bhist S, seminormedSpace_decode_encode_bhist N,
        seminormedSpace_decode_encode_bhist A, seminormedSpace_decode_encode_bhist M,
        seminormedSpace_decode_encode_bhist T, seminormedSpace_decode_encode_bhist C,
        seminormedSpace_decode_encode_bhist P, seminormedSpace_decode_encode_bhist L,
        seminormedSpace_decode_encode_bhist H, seminormedSpace_decode_encode_bhist R]

private theorem seminormedSpaceToEventFlow_injective {x y : SeminormedSpaceUp} :
    seminormedSpaceToEventFlow x = seminormedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow x) =
        seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow y) :=
    congrArg seminormedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (seminormedSpace_round_trip x).symm
      (Eq.trans hread (seminormedSpace_round_trip y)))

instance seminormedSpaceBHistCarrier : BHistCarrier SeminormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := seminormedSpaceToEventFlow
  fromEventFlow := seminormedSpaceFromEventFlow

instance seminormedSpaceChapterTasteGate : ChapterTasteGate SeminormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change seminormedSpaceFromEventFlow (seminormedSpaceToEventFlow x) = some x
    exact seminormedSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (seminormedSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SeminormedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  seminormedSpaceChapterTasteGate

theorem SeminormedSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, seminormedSpaceDecodeBHist (seminormedSpaceEncodeBHist h) = h) ∧
      seminormedSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.SeminormedSpaceUp
