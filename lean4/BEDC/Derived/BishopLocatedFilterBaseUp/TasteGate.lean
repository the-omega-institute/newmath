import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedFilterBaseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedFilterBaseUp : Type where
  | mk (F L W D R E H C P N : BHist) : BishopLocatedFilterBaseUp
  deriving DecidableEq

def BishopLocatedFilterBaseUp_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BishopLocatedFilterBaseUp_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BishopLocatedFilterBaseUp_encodeBHist h

def BishopLocatedFilterBaseUp_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (BishopLocatedFilterBaseUp_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (BishopLocatedFilterBaseUp_decodeBHist tail)

private theorem BishopLocatedFilterBaseUp_decode_encode :
    ∀ h : BHist,
      BishopLocatedFilterBaseUp_decodeBHist
        (BishopLocatedFilterBaseUp_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem BishopLocatedFilterBaseUp_encode_injective {h k : BHist} :
    BishopLocatedFilterBaseUp_encodeBHist h =
      BishopLocatedFilterBaseUp_encodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      BishopLocatedFilterBaseUp_decodeBHist
          (BishopLocatedFilterBaseUp_encodeBHist h) =
        BishopLocatedFilterBaseUp_decodeBHist
          (BishopLocatedFilterBaseUp_encodeBHist k) :=
    congrArg BishopLocatedFilterBaseUp_decodeBHist heq
  exact
    Eq.trans
      (BishopLocatedFilterBaseUp_decode_encode h).symm
      (Eq.trans hdecode (BishopLocatedFilterBaseUp_decode_encode k))

def BishopLocatedFilterBaseUp_fields :
    BishopLocatedFilterBaseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedFilterBaseUp.mk F L W D R E H C P N => [F, L, W, D, R, E, H, C, P, N]

def BishopLocatedFilterBaseUp_toEventFlow :
    BishopLocatedFilterBaseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (BishopLocatedFilterBaseUp_fields x).map BishopLocatedFilterBaseUp_encodeBHist

def BishopLocatedFilterBaseUp_fromEventFlow :
    EventFlow → Option BishopLocatedFilterBaseUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: L :: W :: D :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (BishopLocatedFilterBaseUp.mk
          (BishopLocatedFilterBaseUp_decodeBHist F)
          (BishopLocatedFilterBaseUp_decodeBHist L)
          (BishopLocatedFilterBaseUp_decodeBHist W)
          (BishopLocatedFilterBaseUp_decodeBHist D)
          (BishopLocatedFilterBaseUp_decodeBHist R)
          (BishopLocatedFilterBaseUp_decodeBHist E)
          (BishopLocatedFilterBaseUp_decodeBHist H)
          (BishopLocatedFilterBaseUp_decodeBHist C)
          (BishopLocatedFilterBaseUp_decodeBHist P)
          (BishopLocatedFilterBaseUp_decodeBHist N))
  | _ => none

private theorem BishopLocatedFilterBaseUp_round_trip :
    ∀ x : BishopLocatedFilterBaseUp,
      BishopLocatedFilterBaseUp_fromEventFlow
        (BishopLocatedFilterBaseUp_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F L W D R E H C P N =>
      change
        some
          (BishopLocatedFilterBaseUp.mk
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist F))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist L))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist W))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist D))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist R))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist E))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist H))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist C))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist P))
            (BishopLocatedFilterBaseUp_decodeBHist
              (BishopLocatedFilterBaseUp_encodeBHist N))) =
          some (BishopLocatedFilterBaseUp.mk F L W D R E H C P N)
      rw [BishopLocatedFilterBaseUp_decode_encode F,
        BishopLocatedFilterBaseUp_decode_encode L,
        BishopLocatedFilterBaseUp_decode_encode W,
        BishopLocatedFilterBaseUp_decode_encode D,
        BishopLocatedFilterBaseUp_decode_encode R,
        BishopLocatedFilterBaseUp_decode_encode E,
        BishopLocatedFilterBaseUp_decode_encode H,
        BishopLocatedFilterBaseUp_decode_encode C,
        BishopLocatedFilterBaseUp_decode_encode P,
        BishopLocatedFilterBaseUp_decode_encode N]

private theorem BishopLocatedFilterBaseUp_toEventFlow_injective
    {x y : BishopLocatedFilterBaseUp} :
    BishopLocatedFilterBaseUp_toEventFlow x =
      BishopLocatedFilterBaseUp_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk F₁ L₁ W₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ L₂ W₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection heq with hF t0
          injection t0 with hL t1
          injection t1 with hW t2
          injection t2 with hD t3
          injection t3 with hR t4
          injection t4 with hE t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          have eF : F₁ = F₂ := BishopLocatedFilterBaseUp_encode_injective hF
          have eL : L₁ = L₂ := BishopLocatedFilterBaseUp_encode_injective hL
          have eW : W₁ = W₂ := BishopLocatedFilterBaseUp_encode_injective hW
          have eD : D₁ = D₂ := BishopLocatedFilterBaseUp_encode_injective hD
          have eR : R₁ = R₂ := BishopLocatedFilterBaseUp_encode_injective hR
          have eE : E₁ = E₂ := BishopLocatedFilterBaseUp_encode_injective hE
          have eH : H₁ = H₂ := BishopLocatedFilterBaseUp_encode_injective hH
          have eC : C₁ = C₂ := BishopLocatedFilterBaseUp_encode_injective hC
          have eP : P₁ = P₂ := BishopLocatedFilterBaseUp_encode_injective hP
          have eN : N₁ = N₂ := BishopLocatedFilterBaseUp_encode_injective hN
          cases eF
          cases eL
          cases eW
          cases eD
          cases eR
          cases eE
          cases eH
          cases eC
          cases eP
          cases eN
          rfl

instance BishopLocatedFilterBaseUp_BHistCarrier :
    BHistCarrier BishopLocatedFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BishopLocatedFilterBaseUp_toEventFlow
  fromEventFlow := BishopLocatedFilterBaseUp_fromEventFlow

instance BishopLocatedFilterBaseUp_ChapterTasteGate :
    ChapterTasteGate BishopLocatedFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BishopLocatedFilterBaseUp_fromEventFlow
        (BishopLocatedFilterBaseUp_toEventFlow x) = some x
    exact BishopLocatedFilterBaseUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedFilterBaseUp_toEventFlow_injective heq)

end BEDC.Derived.BishopLocatedFilterBaseUp
