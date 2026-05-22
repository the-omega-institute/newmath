import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMultiplicationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMultiplicationUp : Type where
  | mk (X Y W D B E M Z H C P N : BHist) : RegularCauchyMultiplicationUp
  deriving DecidableEq

def regularCauchyMultiplicationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMultiplicationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMultiplicationEncodeBHist h

def regularCauchyMultiplicationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMultiplicationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMultiplicationDecodeBHist tail)

private theorem regularCauchyMultiplication_decode_encode :
    ∀ h : BHist,
      regularCauchyMultiplicationDecodeBHist
          (regularCauchyMultiplicationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMultiplicationFields :
    RegularCauchyMultiplicationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMultiplicationUp.mk X Y W D B E M Z H C P N =>
      [X, Y, W, D, B, E, M, Z, H, C, P, N]

def regularCauchyMultiplicationToEventFlow :
    RegularCauchyMultiplicationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMultiplicationUp.mk X Y W D B E M Z H C P N =>
      [regularCauchyMultiplicationEncodeBHist X,
        regularCauchyMultiplicationEncodeBHist Y,
        regularCauchyMultiplicationEncodeBHist W,
        regularCauchyMultiplicationEncodeBHist D,
        regularCauchyMultiplicationEncodeBHist B,
        regularCauchyMultiplicationEncodeBHist E,
        regularCauchyMultiplicationEncodeBHist M,
        regularCauchyMultiplicationEncodeBHist Z,
        regularCauchyMultiplicationEncodeBHist H,
        regularCauchyMultiplicationEncodeBHist C,
        regularCauchyMultiplicationEncodeBHist P,
        regularCauchyMultiplicationEncodeBHist N]

def regularCauchyMultiplicationFromEventFlow :
    EventFlow → Option RegularCauchyMultiplicationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: restY =>
      match restY with
      | [] => none
      | Y :: restW =>
          match restW with
          | [] => none
          | W :: restD =>
              match restD with
              | [] => none
              | D :: restB =>
                  match restB with
                  | [] => none
                  | B :: restE =>
                      match restE with
                      | [] => none
                      | E :: restM =>
                          match restM with
                          | [] => none
                          | M :: restZ =>
                              match restZ with
                              | [] => none
                              | Z :: restH =>
                                  match restH with
                                  | [] => none
                                  | H :: restC =>
                                      match restC with
                                      | [] => none
                                      | C :: restP =>
                                          match restP with
                                          | [] => none
                                          | P :: restN =>
                                              match restN with
                                              | [] => none
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (RegularCauchyMultiplicationUp.mk
                                                          (regularCauchyMultiplicationDecodeBHist X)
                                                          (regularCauchyMultiplicationDecodeBHist Y)
                                                          (regularCauchyMultiplicationDecodeBHist W)
                                                          (regularCauchyMultiplicationDecodeBHist D)
                                                          (regularCauchyMultiplicationDecodeBHist B)
                                                          (regularCauchyMultiplicationDecodeBHist E)
                                                          (regularCauchyMultiplicationDecodeBHist M)
                                                          (regularCauchyMultiplicationDecodeBHist Z)
                                                          (regularCauchyMultiplicationDecodeBHist H)
                                                          (regularCauchyMultiplicationDecodeBHist C)
                                                          (regularCauchyMultiplicationDecodeBHist P)
                                                          (regularCauchyMultiplicationDecodeBHist N))
                                                  | _ :: _ => none

private theorem regularCauchyMultiplication_round_trip :
    ∀ x : RegularCauchyMultiplicationUp,
      regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D B E M Z H C P N =>
      change
        some
          (RegularCauchyMultiplicationUp.mk
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist X))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist Y))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist W))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist D))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist B))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist E))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist M))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist Z))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist H))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist C))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist P))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist N))) =
          some (RegularCauchyMultiplicationUp.mk X Y W D B E M Z H C P N)
      rw [regularCauchyMultiplication_decode_encode X,
        regularCauchyMultiplication_decode_encode Y,
        regularCauchyMultiplication_decode_encode W,
        regularCauchyMultiplication_decode_encode D,
        regularCauchyMultiplication_decode_encode B,
        regularCauchyMultiplication_decode_encode E,
        regularCauchyMultiplication_decode_encode M,
        regularCauchyMultiplication_decode_encode Z,
        regularCauchyMultiplication_decode_encode H,
        regularCauchyMultiplication_decode_encode C,
        regularCauchyMultiplication_decode_encode P,
        regularCauchyMultiplication_decode_encode N]

private theorem regularCauchyMultiplicationToEventFlow_injective
    {x y : RegularCauchyMultiplicationUp} :
    regularCauchyMultiplicationToEventFlow x =
        regularCauchyMultiplicationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk X₁ Y₁ W₁ D₁ B₁ E₁ M₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ W₂ D₂ B₂ E₂ M₂ Z₂ H₂ C₂ P₂ N₂ =>
          injection heq with hX tail0
          injection tail0 with hY tail1
          injection tail1 with hW tail2
          injection tail2 with hD tail3
          injection tail3 with hB tail4
          injection tail4 with hE tail5
          injection tail5 with hM tail6
          injection tail6 with hZ tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          have eX : X₁ = X₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode X₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hX)
                (regularCauchyMultiplication_decode_encode X₂))
          have eY : Y₁ = Y₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode Y₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hY)
                (regularCauchyMultiplication_decode_encode Y₂))
          have eW : W₁ = W₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode W₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hW)
                (regularCauchyMultiplication_decode_encode W₂))
          have eD : D₁ = D₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode D₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hD)
                (regularCauchyMultiplication_decode_encode D₂))
          have eB : B₁ = B₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode B₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hB)
                (regularCauchyMultiplication_decode_encode B₂))
          have eE : E₁ = E₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode E₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hE)
                (regularCauchyMultiplication_decode_encode E₂))
          have eM : M₁ = M₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode M₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hM)
                (regularCauchyMultiplication_decode_encode M₂))
          have eZ : Z₁ = Z₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode Z₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hZ)
                (regularCauchyMultiplication_decode_encode Z₂))
          have eH : H₁ = H₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode H₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hH)
                (regularCauchyMultiplication_decode_encode H₂))
          have eC : C₁ = C₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode C₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hC)
                (regularCauchyMultiplication_decode_encode C₂))
          have eP : P₁ = P₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode P₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hP)
                (regularCauchyMultiplication_decode_encode P₂))
          have eN : N₁ = N₂ :=
            Eq.trans (regularCauchyMultiplication_decode_encode N₁).symm
              (Eq.trans (congrArg regularCauchyMultiplicationDecodeBHist hN)
                (regularCauchyMultiplication_decode_encode N₂))
          subst eX; subst eY; subst eW; subst eD; subst eB; subst eE
          subst eM; subst eZ; subst eH; subst eC; subst eP; subst eN
          rfl

private theorem regularCauchyMultiplicationFields_faithful :
    ∀ x y : RegularCauchyMultiplicationUp,
      regularCauchyMultiplicationFields x =
          regularCauchyMultiplicationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ W₁ D₁ B₁ E₁ M₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ W₂ D₂ B₂ E₂ M₂ Z₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX tail0
          injection tail0 with hY tail1
          injection tail1 with hW tail2
          injection tail2 with hD tail3
          injection tail3 with hB tail4
          injection tail4 with hE tail5
          injection tail5 with hM tail6
          injection tail6 with hZ tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hX; subst hY; subst hW; subst hD; subst hB; subst hE
          subst hM; subst hZ; subst hH; subst hC; subst hP; subst hN
          rfl

instance regularCauchyMultiplicationBHistCarrier :
    BHistCarrier RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMultiplicationToEventFlow
  fromEventFlow := regularCauchyMultiplicationFromEventFlow

instance regularCauchyMultiplicationChapterTasteGate :
    ChapterTasteGate RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow x) =
        some x
    exact regularCauchyMultiplication_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMultiplicationToEventFlow_injective heq)

instance regularCauchyMultiplicationFieldFaithful :
    FieldFaithful RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyMultiplicationFields
  field_faithful := regularCauchyMultiplicationFields_faithful

instance regularCauchyMultiplicationNontrivial :
    Nontrivial RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyMultiplicationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyMultiplicationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyMultiplicationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMultiplicationChapterTasteGate

theorem RegularCauchyMultiplicationUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyMultiplicationDecodeBHist
          (regularCauchyMultiplicationEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyMultiplicationUp,
        regularCauchyMultiplicationFromEventFlow
            (regularCauchyMultiplicationToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyMultiplicationUp,
          regularCauchyMultiplicationToEventFlow x =
              regularCauchyMultiplicationToEventFlow y →
            x = y) ∧
          regularCauchyMultiplicationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyMultiplication_decode_encode,
      regularCauchyMultiplication_round_trip,
      by
        intro x y heq
        exact regularCauchyMultiplicationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyMultiplicationUp
