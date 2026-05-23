import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICFrontierDependencyMatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICFrontierDependencyMatrixUp : Type where
  | mk (B A L P Q N D J R H C K : BHist) : MetaCICFrontierDependencyMatrixUp
  deriving DecidableEq

def metaCICFrontierDependencyMatrixEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICFrontierDependencyMatrixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICFrontierDependencyMatrixEncodeBHist h

def metaCICFrontierDependencyMatrixDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => metaCICFrontierDependencyMatrixDecodeBHist tail |> BHist.e0
  | BMark.b1 :: tail => metaCICFrontierDependencyMatrixDecodeBHist tail |> BHist.e1

private theorem metaCICFrontierDependencyMatrixDecode_encode_bhist :
    ∀ h : BHist,
      metaCICFrontierDependencyMatrixDecodeBHist
        (metaCICFrontierDependencyMatrixEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICFrontierDependencyMatrixFields :
    MetaCICFrontierDependencyMatrixUp → List BHist
  | MetaCICFrontierDependencyMatrixUp.mk B A L P Q N D J R H C K =>
      [B, A, L, P, Q, N, D, J, R, H, C, K]

def metaCICFrontierDependencyMatrixToEventFlow :
    MetaCICFrontierDependencyMatrixUp → EventFlow
  | x =>
      (metaCICFrontierDependencyMatrixFields x).map
        metaCICFrontierDependencyMatrixEncodeBHist

def metaCICFrontierDependencyMatrixFromEventFlow :
    EventFlow → Option MetaCICFrontierDependencyMatrixUp
  | B :: A :: L :: P :: Q :: N :: D :: J :: R :: H :: C :: K :: [] =>
      some
        (MetaCICFrontierDependencyMatrixUp.mk
          (metaCICFrontierDependencyMatrixDecodeBHist B)
          (metaCICFrontierDependencyMatrixDecodeBHist A)
          (metaCICFrontierDependencyMatrixDecodeBHist L)
          (metaCICFrontierDependencyMatrixDecodeBHist P)
          (metaCICFrontierDependencyMatrixDecodeBHist Q)
          (metaCICFrontierDependencyMatrixDecodeBHist N)
          (metaCICFrontierDependencyMatrixDecodeBHist D)
          (metaCICFrontierDependencyMatrixDecodeBHist J)
          (metaCICFrontierDependencyMatrixDecodeBHist R)
          (metaCICFrontierDependencyMatrixDecodeBHist H)
          (metaCICFrontierDependencyMatrixDecodeBHist C)
          (metaCICFrontierDependencyMatrixDecodeBHist K))
  | _ => none

private theorem metaCICFrontierDependencyMatrix_round_trip :
    ∀ x : MetaCICFrontierDependencyMatrixUp,
      metaCICFrontierDependencyMatrixFromEventFlow
        (metaCICFrontierDependencyMatrixToEventFlow x) = some x := by
  intro x
  cases x with
  | mk B A L P Q N D J R H C K =>
      change
        some
          (MetaCICFrontierDependencyMatrixUp.mk
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist B))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist A))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist L))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist P))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist Q))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist N))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist D))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist J))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist R))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist H))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist C))
            (metaCICFrontierDependencyMatrixDecodeBHist
              (metaCICFrontierDependencyMatrixEncodeBHist K))) =
          some (MetaCICFrontierDependencyMatrixUp.mk B A L P Q N D J R H C K)
      rw [metaCICFrontierDependencyMatrixDecode_encode_bhist B,
        metaCICFrontierDependencyMatrixDecode_encode_bhist A,
        metaCICFrontierDependencyMatrixDecode_encode_bhist L,
        metaCICFrontierDependencyMatrixDecode_encode_bhist P,
        metaCICFrontierDependencyMatrixDecode_encode_bhist Q,
        metaCICFrontierDependencyMatrixDecode_encode_bhist N,
        metaCICFrontierDependencyMatrixDecode_encode_bhist D,
        metaCICFrontierDependencyMatrixDecode_encode_bhist J,
        metaCICFrontierDependencyMatrixDecode_encode_bhist R,
        metaCICFrontierDependencyMatrixDecode_encode_bhist H,
        metaCICFrontierDependencyMatrixDecode_encode_bhist C,
        metaCICFrontierDependencyMatrixDecode_encode_bhist K]

private theorem metaCICFrontierDependencyMatrixToEventFlow_injective
    {x y : MetaCICFrontierDependencyMatrixUp} :
    metaCICFrontierDependencyMatrixToEventFlow x =
      metaCICFrontierDependencyMatrixToEventFlow y → x = y := by
  intro heq
  have hread :
      metaCICFrontierDependencyMatrixFromEventFlow
          (metaCICFrontierDependencyMatrixToEventFlow x) =
        metaCICFrontierDependencyMatrixFromEventFlow
          (metaCICFrontierDependencyMatrixToEventFlow y) :=
    congrArg metaCICFrontierDependencyMatrixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICFrontierDependencyMatrix_round_trip x).symm
      (Eq.trans hread (metaCICFrontierDependencyMatrix_round_trip y)))

private theorem metaCICFrontierDependencyMatrix_fields_faithful :
    ∀ x y : MetaCICFrontierDependencyMatrixUp,
      metaCICFrontierDependencyMatrixFields x =
        metaCICFrontierDependencyMatrixFields y → x = y := by
  intro x y hfields
  cases x with
  | mk B A L P Q N D J R H C K =>
      cases y with
      | mk B' A' L' P' Q' N' D' J' R' H' C' K' =>
          cases hfields
          rfl

instance metaCICFrontierDependencyMatrixBHistCarrier :
    BHistCarrier MetaCICFrontierDependencyMatrixUp where
  toEventFlow := metaCICFrontierDependencyMatrixToEventFlow
  fromEventFlow := metaCICFrontierDependencyMatrixFromEventFlow

instance metaCICFrontierDependencyMatrixChapterTasteGate :
    ChapterTasteGate MetaCICFrontierDependencyMatrixUp where
  round_trip := by
    intro x
    exact metaCICFrontierDependencyMatrix_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICFrontierDependencyMatrixToEventFlow_injective heq)

instance metaCICFrontierDependencyMatrixFieldFaithful :
    FieldFaithful MetaCICFrontierDependencyMatrixUp where
  fields := metaCICFrontierDependencyMatrixFields
  field_faithful := metaCICFrontierDependencyMatrix_fields_faithful

instance metaCICFrontierDependencyMatrixNontrivial :
    Nontrivial MetaCICFrontierDependencyMatrixUp where
  witness_pair :=
    ⟨MetaCICFrontierDependencyMatrixUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      MetaCICFrontierDependencyMatrixUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICFrontierDependencyMatrixUp :=
  metaCICFrontierDependencyMatrixChapterTasteGate

def MetaCICFrontierDependencyMatrixTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metaCICFrontierDependencyMatrixDecodeBHist
          (metaCICFrontierDependencyMatrixEncodeBHist h) = h) ∧
      (∀ x : MetaCICFrontierDependencyMatrixUp,
        metaCICFrontierDependencyMatrixFromEventFlow
          (metaCICFrontierDependencyMatrixToEventFlow x) = some x) ∧
      (∀ x y : MetaCICFrontierDependencyMatrixUp,
        metaCICFrontierDependencyMatrixToEventFlow x =
          metaCICFrontierDependencyMatrixToEventFlow y → x = y) ∧
      metaCICFrontierDependencyMatrixEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact ⟨metaCICFrontierDependencyMatrixDecode_encode_bhist,
    metaCICFrontierDependencyMatrix_round_trip,
    fun _ _ heq => metaCICFrontierDependencyMatrixToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.MetaCICFrontierDependencyMatrixUp
