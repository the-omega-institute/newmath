import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionReflectorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionReflectorUp : Type where
  | mk (X W Y J Q H C P N : BHist) : UniformCompletionReflectorUp
  deriving DecidableEq

def uniformCompletionReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionReflectorEncodeBHist h

def uniformCompletionReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionReflectorDecodeBHist tail)

private theorem uniformCompletionReflectorDecode_encode_bhist :
    ∀ h : BHist,
      uniformCompletionReflectorDecodeBHist
        (uniformCompletionReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformCompletionReflectorFields :
    UniformCompletionReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionReflectorUp.mk X W Y J Q H C P N =>
      [X, W, Y, J, Q, H, C, P, N]

def uniformCompletionReflectorToEventFlow :
    UniformCompletionReflectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (uniformCompletionReflectorFields x).map
        uniformCompletionReflectorEncodeBHist

def uniformCompletionReflectorFromEventFlow :
    EventFlow → Option UniformCompletionReflectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | Y :: rest2 =>
              match rest2 with
              | [] => none
              | J :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (UniformCompletionReflectorUp.mk
                                              (uniformCompletionReflectorDecodeBHist X)
                                              (uniformCompletionReflectorDecodeBHist W)
                                              (uniformCompletionReflectorDecodeBHist Y)
                                              (uniformCompletionReflectorDecodeBHist J)
                                              (uniformCompletionReflectorDecodeBHist Q)
                                              (uniformCompletionReflectorDecodeBHist H)
                                              (uniformCompletionReflectorDecodeBHist C)
                                              (uniformCompletionReflectorDecodeBHist P)
                                              (uniformCompletionReflectorDecodeBHist N))
                                      | _ :: _ => none

private theorem uniformCompletionReflector_round_trip :
    ∀ x : UniformCompletionReflectorUp,
      uniformCompletionReflectorFromEventFlow
        (uniformCompletionReflectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X W Y J Q H C P N =>
      change
        some
          (UniformCompletionReflectorUp.mk
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist X))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist W))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist Y))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist J))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist Q))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist H))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist C))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist P))
            (uniformCompletionReflectorDecodeBHist
              (uniformCompletionReflectorEncodeBHist N))) =
          some (UniformCompletionReflectorUp.mk X W Y J Q H C P N)
      rw [uniformCompletionReflectorDecode_encode_bhist X,
        uniformCompletionReflectorDecode_encode_bhist W,
        uniformCompletionReflectorDecode_encode_bhist Y,
        uniformCompletionReflectorDecode_encode_bhist J,
        uniformCompletionReflectorDecode_encode_bhist Q,
        uniformCompletionReflectorDecode_encode_bhist H,
        uniformCompletionReflectorDecode_encode_bhist C,
        uniformCompletionReflectorDecode_encode_bhist P,
        uniformCompletionReflectorDecode_encode_bhist N]

private theorem uniformCompletionReflectorToEventFlow_injective
    {x y : UniformCompletionReflectorUp} :
    uniformCompletionReflectorToEventFlow x =
        uniformCompletionReflectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk X₁ W₁ Y₁ J₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ W₂ Y₂ J₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection heq with hX tail0
          injection tail0 with hW tail1
          injection tail1 with hY tail2
          injection tail2 with hJ tail3
          injection tail3 with hQ tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          have dX :
              X₁ = X₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist X₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hX)
                (uniformCompletionReflectorDecode_encode_bhist X₂))
          have dW :
              W₁ = W₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist W₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hW)
                (uniformCompletionReflectorDecode_encode_bhist W₂))
          have dY :
              Y₁ = Y₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist Y₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hY)
                (uniformCompletionReflectorDecode_encode_bhist Y₂))
          have dJ :
              J₁ = J₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist J₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hJ)
                (uniformCompletionReflectorDecode_encode_bhist J₂))
          have dQ :
              Q₁ = Q₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist Q₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hQ)
                (uniformCompletionReflectorDecode_encode_bhist Q₂))
          have dH :
              H₁ = H₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist H₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hH)
                (uniformCompletionReflectorDecode_encode_bhist H₂))
          have dC :
              C₁ = C₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist C₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hC)
                (uniformCompletionReflectorDecode_encode_bhist C₂))
          have dP :
              P₁ = P₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist P₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hP)
                (uniformCompletionReflectorDecode_encode_bhist P₂))
          have dN :
              N₁ = N₂ :=
            Eq.trans (uniformCompletionReflectorDecode_encode_bhist N₁).symm
              (Eq.trans (congrArg uniformCompletionReflectorDecodeBHist hN)
                (uniformCompletionReflectorDecode_encode_bhist N₂))
          cases dX
          cases dW
          cases dY
          cases dJ
          cases dQ
          cases dH
          cases dC
          cases dP
          cases dN
          rfl

instance uniformCompletionReflectorBHistCarrier :
    BHistCarrier UniformCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionReflectorToEventFlow
  fromEventFlow := uniformCompletionReflectorFromEventFlow

instance uniformCompletionReflectorChapterTasteGate :
    ChapterTasteGate UniformCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCompletionReflectorFromEventFlow
        (uniformCompletionReflectorToEventFlow x) = some x
    exact uniformCompletionReflector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCompletionReflectorToEventFlow_injective heq)

theorem UniformCompletionReflectorTasteGate_single_carrier_alignment :
    (∀ X W Y J Q H C P N : BHist,
      uniformCompletionReflectorFields
          (UniformCompletionReflectorUp.mk X W Y J Q H C P N) =
        [X, W, Y, J, Q, H, C, P, N]) ∧
      (∀ X W Y J Q H C P N : BHist,
        uniformCompletionReflectorToEventFlow
            (UniformCompletionReflectorUp.mk X W Y J Q H C P N) =
          [uniformCompletionReflectorEncodeBHist X,
            uniformCompletionReflectorEncodeBHist W,
            uniformCompletionReflectorEncodeBHist Y,
            uniformCompletionReflectorEncodeBHist J,
            uniformCompletionReflectorEncodeBHist Q,
            uniformCompletionReflectorEncodeBHist H,
            uniformCompletionReflectorEncodeBHist C,
            uniformCompletionReflectorEncodeBHist P,
            uniformCompletionReflectorEncodeBHist N]) ∧
        (∀ h : BHist,
          uniformCompletionReflectorDecodeBHist
            (uniformCompletionReflectorEncodeBHist h) = h) ∧
          uniformCompletionReflectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro X W Y J Q H C P N
    rfl
  · constructor
    · intro X W Y J Q H C P N
      rfl
    · constructor
      · exact uniformCompletionReflectorDecode_encode_bhist
      · rfl

end BEDC.Derived.UniformCompletionReflectorUp.TasteGate
