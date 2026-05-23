import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IsometricEmbeddingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IsometricEmbeddingUp : Type where
  | mk (X Y F DX DY R T Q P N : BHist) : IsometricEmbeddingUp
  deriving DecidableEq

def isometricEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: isometricEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: isometricEmbeddingEncodeBHist h

def isometricEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (isometricEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (isometricEmbeddingDecodeBHist tail)

private theorem isometricEmbedding_decode_encode :
    ∀ h : BHist, isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem isometricEmbedding_mk_congr
    {X1 X2 Y1 Y2 F1 F2 DX1 DX2 DY1 DY2 R1 R2 T1 T2 Q1 Q2 P1 P2 N1 N2 : BHist}
    (hX : X1 = X2) (hY : Y1 = Y2) (hF : F1 = F2) (hDX : DX1 = DX2)
    (hDY : DY1 = DY2) (hR : R1 = R2) (hT : T1 = T2) (hQ : Q1 = Q2)
    (hP : P1 = P2) (hN : N1 = N2) :
    IsometricEmbeddingUp.mk X1 Y1 F1 DX1 DY1 R1 T1 Q1 P1 N1 =
      IsometricEmbeddingUp.mk X2 Y2 F2 DX2 DY2 R2 T2 Q2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hF
  cases hDX
  cases hDY
  cases hR
  cases hT
  cases hQ
  cases hP
  cases hN
  rfl

def isometricEmbeddingFields : IsometricEmbeddingUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | IsometricEmbeddingUp.mk X Y F DX DY R T Q P N => [X, Y, F, DX, DY, R, T, Q, P, N]

def isometricEmbeddingToEventFlow : IsometricEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | IsometricEmbeddingUp.mk X Y F DX DY R T Q P N =>
      [isometricEmbeddingEncodeBHist X,
        isometricEmbeddingEncodeBHist Y,
        isometricEmbeddingEncodeBHist F,
        isometricEmbeddingEncodeBHist DX,
        isometricEmbeddingEncodeBHist DY,
        isometricEmbeddingEncodeBHist R,
        isometricEmbeddingEncodeBHist T,
        isometricEmbeddingEncodeBHist Q,
        isometricEmbeddingEncodeBHist P,
        isometricEmbeddingEncodeBHist N]

def isometricEmbeddingFromEventFlow : EventFlow → Option IsometricEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | _X :: [] => none
  | _X :: _Y :: [] => none
  | _X :: _Y :: _F :: [] => none
  | _X :: _Y :: _F :: _DX :: [] => none
  | _X :: _Y :: _F :: _DX :: _DY :: [] => none
  | _X :: _Y :: _F :: _DX :: _DY :: _R :: [] => none
  | _X :: _Y :: _F :: _DX :: _DY :: _R :: _T :: [] => none
  | _X :: _Y :: _F :: _DX :: _DY :: _R :: _T :: _Q :: [] => none
  | _X :: _Y :: _F :: _DX :: _DY :: _R :: _T :: _Q :: _P :: [] => none
  | X :: Y :: F :: DX :: DY :: R :: T :: Q :: P :: N :: [] =>
      some
        (IsometricEmbeddingUp.mk
          (isometricEmbeddingDecodeBHist X)
          (isometricEmbeddingDecodeBHist Y)
          (isometricEmbeddingDecodeBHist F)
          (isometricEmbeddingDecodeBHist DX)
          (isometricEmbeddingDecodeBHist DY)
          (isometricEmbeddingDecodeBHist R)
          (isometricEmbeddingDecodeBHist T)
          (isometricEmbeddingDecodeBHist Q)
          (isometricEmbeddingDecodeBHist P)
          (isometricEmbeddingDecodeBHist N))
  | _X :: _Y :: _F :: _DX :: _DY :: _R :: _T :: _Q :: _P :: _N :: _extra :: _rest =>
      none

private theorem isometricEmbedding_round_trip :
    ∀ x : IsometricEmbeddingUp,
      isometricEmbeddingFromEventFlow (isometricEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y F DX DY R T Q P N =>
      exact
        Eq.trans
          (congrArg
            (fun z =>
              some
                (IsometricEmbeddingUp.mk z
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Y))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist F))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist DX))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist DY))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist R))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist T))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Q))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist P))
                  (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist N))))
            (isometricEmbedding_decode_encode X))
          (Eq.trans
            (congrArg
              (fun z =>
                some
                  (IsometricEmbeddingUp.mk X z
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist F))
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist DX))
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist DY))
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist R))
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist T))
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Q))
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist P))
                    (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist N))))
              (isometricEmbedding_decode_encode Y))
            (Eq.trans
              (congrArg
                (fun z =>
                  some
                    (IsometricEmbeddingUp.mk X Y z
                      (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist DX))
                      (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist DY))
                      (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist R))
                      (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist T))
                      (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Q))
                      (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist P))
                      (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist N))))
                (isometricEmbedding_decode_encode F))
              (Eq.trans
                (congrArg
                  (fun z =>
                    some
                      (IsometricEmbeddingUp.mk X Y F z
                        (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist DY))
                        (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist R))
                        (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist T))
                        (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Q))
                        (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist P))
                        (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist N))))
                  (isometricEmbedding_decode_encode DX))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      some
                        (IsometricEmbeddingUp.mk X Y F DX z
                          (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist R))
                          (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist T))
                          (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Q))
                          (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist P))
                          (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist N))))
                    (isometricEmbedding_decode_encode DY))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        some
                          (IsometricEmbeddingUp.mk X Y F DX DY z
                            (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist T))
                            (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Q))
                            (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist P))
                            (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist N))))
                      (isometricEmbedding_decode_encode R))
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          some
                            (IsometricEmbeddingUp.mk X Y F DX DY R z
                              (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist Q))
                              (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist P))
                              (isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist N))))
                        (isometricEmbedding_decode_encode T))
                      (Eq.trans
                        (congrArg
                          (fun z =>
                            some
                              (IsometricEmbeddingUp.mk X Y F DX DY R T z
                                (isometricEmbeddingDecodeBHist
                                  (isometricEmbeddingEncodeBHist P))
                                (isometricEmbeddingDecodeBHist
                                  (isometricEmbeddingEncodeBHist N))))
                          (isometricEmbedding_decode_encode Q))
                        (Eq.trans
                          (congrArg
                            (fun z =>
                              some
                                (IsometricEmbeddingUp.mk X Y F DX DY R T Q z
                                  (isometricEmbeddingDecodeBHist
                                    (isometricEmbeddingEncodeBHist N))))
                            (isometricEmbedding_decode_encode P))
                          (congrArg
                            (fun z => some (IsometricEmbeddingUp.mk X Y F DX DY R T Q P z))
                            (isometricEmbedding_decode_encode N))))))))))

private theorem isometricEmbeddingToEventFlow_injective {x y : IsometricEmbeddingUp} :
    isometricEmbeddingToEventFlow x = isometricEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      isometricEmbeddingFromEventFlow (isometricEmbeddingToEventFlow x) =
        isometricEmbeddingFromEventFlow (isometricEmbeddingToEventFlow y) :=
    congrArg isometricEmbeddingFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (isometricEmbedding_round_trip x).symm
      (Eq.trans hread (isometricEmbedding_round_trip y)))

instance isometricEmbeddingBHistCarrier : BHistCarrier IsometricEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := isometricEmbeddingToEventFlow
  fromEventFlow := isometricEmbeddingFromEventFlow

instance isometricEmbeddingChapterTasteGate : ChapterTasteGate IsometricEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change isometricEmbeddingFromEventFlow (isometricEmbeddingToEventFlow x) = some x
    exact isometricEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (isometricEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate IsometricEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  isometricEmbeddingChapterTasteGate

theorem IsometricEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist, isometricEmbeddingDecodeBHist (isometricEmbeddingEncodeBHist h) = h) ∧
      (∀ x : IsometricEmbeddingUp,
        isometricEmbeddingFromEventFlow (isometricEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : IsometricEmbeddingUp,
        isometricEmbeddingToEventFlow x = isometricEmbeddingToEventFlow y → x = y) ∧
      isometricEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact isometricEmbedding_decode_encode h
  · constructor
    · intro x
      exact isometricEmbedding_round_trip x
    · constructor
      · intro x y hxy
        have hread :
            isometricEmbeddingFromEventFlow (isometricEmbeddingToEventFlow x) =
              isometricEmbeddingFromEventFlow (isometricEmbeddingToEventFlow y) :=
          congrArg isometricEmbeddingFromEventFlow hxy
        have hsome : some x = some y :=
          Eq.trans (isometricEmbedding_round_trip x).symm
            (Eq.trans hread (isometricEmbedding_round_trip y))
        exact Option.some.inj hsome
      · rfl

end BEDC.Derived.IsometricEmbeddingUp.TasteGate
