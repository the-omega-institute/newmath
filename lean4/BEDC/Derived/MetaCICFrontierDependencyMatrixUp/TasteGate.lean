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
  | BMark.b0 :: tail =>
      BHist.e0 (metaCICFrontierDependencyMatrixDecodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (metaCICFrontierDependencyMatrixDecodeBHist tail)

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
  | MetaCICFrontierDependencyMatrixUp.mk B A L P Q N D J R H C K =>
      [metaCICFrontierDependencyMatrixEncodeBHist B,
        metaCICFrontierDependencyMatrixEncodeBHist A,
        metaCICFrontierDependencyMatrixEncodeBHist L,
        metaCICFrontierDependencyMatrixEncodeBHist P,
        metaCICFrontierDependencyMatrixEncodeBHist Q,
        metaCICFrontierDependencyMatrixEncodeBHist N,
        metaCICFrontierDependencyMatrixEncodeBHist D,
        metaCICFrontierDependencyMatrixEncodeBHist J,
        metaCICFrontierDependencyMatrixEncodeBHist R,
        metaCICFrontierDependencyMatrixEncodeBHist H,
        metaCICFrontierDependencyMatrixEncodeBHist C,
        metaCICFrontierDependencyMatrixEncodeBHist K]

private def metaCICFrontierDependencyMatrixEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICFrontierDependencyMatrixEventAt index rest

def metaCICFrontierDependencyMatrixFromEventFlow :
    EventFlow → Option MetaCICFrontierDependencyMatrixUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MetaCICFrontierDependencyMatrixUp.mk
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 0 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 1 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 2 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 3 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 4 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 5 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 6 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 7 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 8 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 9 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 10 ef))
          (metaCICFrontierDependencyMatrixDecodeBHist
            (metaCICFrontierDependencyMatrixEventAt 11 ef)))

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
          injection hfields with hB tail0
          injection tail0 with hA tail1
          injection tail1 with hL tail2
          injection tail2 with hP tail3
          injection tail3 with hQ tail4
          injection tail4 with hN tail5
          injection tail5 with hD tail6
          injection tail6 with hJ tail7
          injection tail7 with hR tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hK _
          subst hB
          subst hA
          subst hL
          subst hP
          subst hQ
          subst hN
          subst hD
          subst hJ
          subst hR
          subst hH
          subst hC
          subst hK
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
  have decodeEncode :
      ∀ h : BHist,
        metaCICFrontierDependencyMatrixDecodeBHist
          (metaCICFrontierDependencyMatrixEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have roundTrip :
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
        rw [decodeEncode B, decodeEncode A, decodeEncode L, decodeEncode P,
          decodeEncode Q, decodeEncode N, decodeEncode D, decodeEncode J,
          decodeEncode R, decodeEncode H, decodeEncode C, decodeEncode K]
  have injective :
      ∀ x y : MetaCICFrontierDependencyMatrixUp,
        metaCICFrontierDependencyMatrixToEventFlow x =
          metaCICFrontierDependencyMatrixToEventFlow y → x = y := by
    intro x y heq
    have hread :
        metaCICFrontierDependencyMatrixFromEventFlow
            (metaCICFrontierDependencyMatrixToEventFlow x) =
          metaCICFrontierDependencyMatrixFromEventFlow
            (metaCICFrontierDependencyMatrixToEventFlow y) :=
      congrArg metaCICFrontierDependencyMatrixFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))
  constructor
  · exact decodeEncode
  · constructor
    · exact roundTrip
    · constructor
      · intro x y heq
        exact injective x y heq
      · rfl

end BEDC.Derived.MetaCICFrontierDependencyMatrixUp
