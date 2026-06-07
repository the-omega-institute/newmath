import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KanExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KanExtensionUp : Type where
  | mk :
      (C D E J F L eta U V H R P N : BHist) →
        KanExtensionUp
  deriving DecidableEq

def kanExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kanExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kanExtensionEncodeBHist h

def kanExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kanExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kanExtensionDecodeBHist tail)

private theorem kanExtensionDecode_encode_bhist :
    ∀ h : BHist, kanExtensionDecodeBHist (kanExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem kanExtension_mk_congr
    {C C' D D' E E' J J' F F' L L' eta eta' U U' V V' H H' R R' P P' N N' :
        BHist}
    (hC : C' = C) (hD : D' = D) (hE : E' = E) (hJ : J' = J) (hF : F' = F)
    (hL : L' = L) (hEta : eta' = eta) (hU : U' = U) (hV : V' = V)
    (hH : H' = H) (hR : R' = R) (hP : P' = P) (hN : N' = N) :
    KanExtensionUp.mk C' D' E' J' F' L' eta' U' V' H' R' P' N' =
      KanExtensionUp.mk C D E J F L eta U V H R P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hD
  cases hE
  cases hJ
  cases hF
  cases hL
  cases hEta
  cases hU
  cases hV
  cases hH
  cases hR
  cases hP
  cases hN
  rfl

def kanExtensionToEventFlow : KanExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KanExtensionUp.mk C D E J F L eta U V H R P N =>
      [kanExtensionEncodeBHist C,
        kanExtensionEncodeBHist D,
        kanExtensionEncodeBHist E,
        kanExtensionEncodeBHist J,
        kanExtensionEncodeBHist F,
        kanExtensionEncodeBHist L,
        kanExtensionEncodeBHist eta,
        kanExtensionEncodeBHist U,
        kanExtensionEncodeBHist V,
        kanExtensionEncodeBHist H,
        kanExtensionEncodeBHist R,
        kanExtensionEncodeBHist P,
        kanExtensionEncodeBHist N]

def kanExtensionFromEventFlow : EventFlow → Option KanExtensionUp
  -- BEDC touchpoint anchor: BHist BMark
  | C :: D :: E :: J :: F :: L :: eta :: U :: V :: H :: R :: P :: N :: [] =>
      some
        (KanExtensionUp.mk
          (kanExtensionDecodeBHist C)
          (kanExtensionDecodeBHist D)
          (kanExtensionDecodeBHist E)
          (kanExtensionDecodeBHist J)
          (kanExtensionDecodeBHist F)
          (kanExtensionDecodeBHist L)
          (kanExtensionDecodeBHist eta)
          (kanExtensionDecodeBHist U)
          (kanExtensionDecodeBHist V)
          (kanExtensionDecodeBHist H)
          (kanExtensionDecodeBHist R)
          (kanExtensionDecodeBHist P)
          (kanExtensionDecodeBHist N))
  | _ => none

private theorem kanExtension_round_trip :
    ∀ x : KanExtensionUp, kanExtensionFromEventFlow (kanExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C D E J F L eta U V H R P N =>
      change
        some
          (KanExtensionUp.mk
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist C))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist D))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist E))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist J))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist F))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist L))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist eta))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist U))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist V))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist H))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist R))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist P))
            (kanExtensionDecodeBHist (kanExtensionEncodeBHist N))) =
          some (KanExtensionUp.mk C D E J F L eta U V H R P N)
      exact
        congrArg some
          (kanExtension_mk_congr
            (kanExtensionDecode_encode_bhist C)
            (kanExtensionDecode_encode_bhist D)
            (kanExtensionDecode_encode_bhist E)
            (kanExtensionDecode_encode_bhist J)
            (kanExtensionDecode_encode_bhist F)
            (kanExtensionDecode_encode_bhist L)
            (kanExtensionDecode_encode_bhist eta)
            (kanExtensionDecode_encode_bhist U)
            (kanExtensionDecode_encode_bhist V)
            (kanExtensionDecode_encode_bhist H)
            (kanExtensionDecode_encode_bhist R)
            (kanExtensionDecode_encode_bhist P)
            (kanExtensionDecode_encode_bhist N))

private theorem kanExtensionToEventFlow_injective {x y : KanExtensionUp} :
    kanExtensionToEventFlow x = kanExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kanExtensionFromEventFlow (kanExtensionToEventFlow x) =
        kanExtensionFromEventFlow (kanExtensionToEventFlow y) :=
    congrArg kanExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kanExtension_round_trip x).symm
      (Eq.trans hread (kanExtension_round_trip y)))

instance kanExtensionBHistCarrier : BHistCarrier KanExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kanExtensionToEventFlow
  fromEventFlow := kanExtensionFromEventFlow

instance kanExtensionChapterTasteGate : ChapterTasteGate KanExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kanExtensionFromEventFlow (kanExtensionToEventFlow x) = some x
    exact kanExtension_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kanExtensionToEventFlow_injective heq)

theorem KanExtensionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, kanExtensionDecodeBHist (kanExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  exact kanExtensionDecode_encode_bhist

def KanExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist, kanExtensionDecodeBHist (kanExtensionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KanExtensionUp) ∧
        Nonempty (ChapterTasteGate KanExtensionUp) ∧
          kanExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨kanExtensionDecode_encode_bhist,
      ⟨⟨kanExtensionBHistCarrier⟩, ⟨kanExtensionChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.KanExtensionUp
