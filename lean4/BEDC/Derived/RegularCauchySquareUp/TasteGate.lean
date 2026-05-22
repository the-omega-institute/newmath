import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySquareUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySquareUp : Type where
  | mk (A W_L W_R D_L D_R M E R Z H C P N : BHist) : RegularCauchySquareUp
  deriving DecidableEq

def regularCauchySquareEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySquareEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySquareEncodeBHist h

def regularCauchySquareDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySquareDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySquareDecodeBHist tail)

private theorem regularCauchySquare_decode_encode :
    ∀ h : BHist,
      regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySquareFields :
    RegularCauchySquareUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySquareUp.mk A W_L W_R D_L D_R M E R Z H C P N =>
      [A, W_L, W_R, D_L, D_R, M, E, R, Z, H, C, P, N]

def regularCauchySquareToEventFlow : RegularCauchySquareUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySquareUp.mk A W_L W_R D_L D_R M E R Z H C P N =>
      [regularCauchySquareEncodeBHist A,
        regularCauchySquareEncodeBHist W_L,
        regularCauchySquareEncodeBHist W_R,
        regularCauchySquareEncodeBHist D_L,
        regularCauchySquareEncodeBHist D_R,
        regularCauchySquareEncodeBHist M,
        regularCauchySquareEncodeBHist E,
        regularCauchySquareEncodeBHist R,
        regularCauchySquareEncodeBHist Z,
        regularCauchySquareEncodeBHist H,
        regularCauchySquareEncodeBHist C,
        regularCauchySquareEncodeBHist P,
        regularCauchySquareEncodeBHist N]

def regularCauchySquareFromEventFlow : EventFlow → Option RegularCauchySquareUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: restWL =>
      match restWL with
      | [] => none
      | W_L :: restWR =>
          match restWR with
          | [] => none
          | W_R :: restDL =>
              match restDL with
              | [] => none
              | D_L :: restDR =>
                  match restDR with
                  | [] => none
                  | D_R :: restM =>
                      match restM with
                      | [] => none
                      | M :: restE =>
                          match restE with
                          | [] => none
                          | E :: restR =>
                              match restR with
                              | [] => none
                              | R :: restZ =>
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
                                                            (RegularCauchySquareUp.mk
                                                              (regularCauchySquareDecodeBHist A)
                                                              (regularCauchySquareDecodeBHist W_L)
                                                              (regularCauchySquareDecodeBHist W_R)
                                                              (regularCauchySquareDecodeBHist D_L)
                                                              (regularCauchySquareDecodeBHist D_R)
                                                              (regularCauchySquareDecodeBHist M)
                                                              (regularCauchySquareDecodeBHist E)
                                                              (regularCauchySquareDecodeBHist R)
                                                              (regularCauchySquareDecodeBHist Z)
                                                              (regularCauchySquareDecodeBHist H)
                                                              (regularCauchySquareDecodeBHist C)
                                                              (regularCauchySquareDecodeBHist P)
                                                              (regularCauchySquareDecodeBHist N))
                                                      | _ :: _ => none

private theorem regularCauchySquare_round_trip :
    ∀ x : RegularCauchySquareUp,
      regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W_L W_R D_L D_R M E R Z H C P N =>
      change
        some
          (RegularCauchySquareUp.mk
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist A))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist W_L))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist W_R))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist D_L))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist D_R))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist M))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist E))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist R))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist Z))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist H))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist C))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist P))
            (regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist N))) =
          some (RegularCauchySquareUp.mk A W_L W_R D_L D_R M E R Z H C P N)
      rw [regularCauchySquare_decode_encode A,
        regularCauchySquare_decode_encode W_L,
        regularCauchySquare_decode_encode W_R,
        regularCauchySquare_decode_encode D_L,
        regularCauchySquare_decode_encode D_R,
        regularCauchySquare_decode_encode M,
        regularCauchySquare_decode_encode E,
        regularCauchySquare_decode_encode R,
        regularCauchySquare_decode_encode Z,
        regularCauchySquare_decode_encode H,
        regularCauchySquare_decode_encode C,
        regularCauchySquare_decode_encode P,
        regularCauchySquare_decode_encode N]

private theorem regularCauchySquareToEventFlow_injective
    {x y : RegularCauchySquareUp} :
    regularCauchySquareToEventFlow x =
        regularCauchySquareToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk A₁ WL₁ WR₁ DL₁ DR₁ M₁ E₁ R₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ WL₂ WR₂ DL₂ DR₂ M₂ E₂ R₂ Z₂ H₂ C₂ P₂ N₂ =>
          injection heq with hA tail0
          injection tail0 with hWL tail1
          injection tail1 with hWR tail2
          injection tail2 with hDL tail3
          injection tail3 with hDR tail4
          injection tail4 with hM tail5
          injection tail5 with hE tail6
          injection tail6 with hR tail7
          injection tail7 with hZ tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hP tail11
          injection tail11 with hN _
          have eA : A₁ = A₂ :=
            Eq.trans (regularCauchySquare_decode_encode A₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hA)
                (regularCauchySquare_decode_encode A₂))
          have eWL : WL₁ = WL₂ :=
            Eq.trans (regularCauchySquare_decode_encode WL₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hWL)
                (regularCauchySquare_decode_encode WL₂))
          have eWR : WR₁ = WR₂ :=
            Eq.trans (regularCauchySquare_decode_encode WR₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hWR)
                (regularCauchySquare_decode_encode WR₂))
          have eDL : DL₁ = DL₂ :=
            Eq.trans (regularCauchySquare_decode_encode DL₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hDL)
                (regularCauchySquare_decode_encode DL₂))
          have eDR : DR₁ = DR₂ :=
            Eq.trans (regularCauchySquare_decode_encode DR₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hDR)
                (regularCauchySquare_decode_encode DR₂))
          have eM : M₁ = M₂ :=
            Eq.trans (regularCauchySquare_decode_encode M₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hM)
                (regularCauchySquare_decode_encode M₂))
          have eE : E₁ = E₂ :=
            Eq.trans (regularCauchySquare_decode_encode E₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hE)
                (regularCauchySquare_decode_encode E₂))
          have eR : R₁ = R₂ :=
            Eq.trans (regularCauchySquare_decode_encode R₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hR)
                (regularCauchySquare_decode_encode R₂))
          have eZ : Z₁ = Z₂ :=
            Eq.trans (regularCauchySquare_decode_encode Z₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hZ)
                (regularCauchySquare_decode_encode Z₂))
          have eH : H₁ = H₂ :=
            Eq.trans (regularCauchySquare_decode_encode H₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hH)
                (regularCauchySquare_decode_encode H₂))
          have eC : C₁ = C₂ :=
            Eq.trans (regularCauchySquare_decode_encode C₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hC)
                (regularCauchySquare_decode_encode C₂))
          have eP : P₁ = P₂ :=
            Eq.trans (regularCauchySquare_decode_encode P₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hP)
                (regularCauchySquare_decode_encode P₂))
          have eN : N₁ = N₂ :=
            Eq.trans (regularCauchySquare_decode_encode N₁).symm
              (Eq.trans (congrArg regularCauchySquareDecodeBHist hN)
                (regularCauchySquare_decode_encode N₂))
          subst eA; subst eWL; subst eWR; subst eDL; subst eDR; subst eM
          subst eE; subst eR; subst eZ; subst eH; subst eC; subst eP; subst eN
          rfl

private theorem regularCauchySquareFields_faithful :
    ∀ x y : RegularCauchySquareUp,
      regularCauchySquareFields x = regularCauchySquareFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ WL₁ WR₁ DL₁ DR₁ M₁ E₁ R₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ WL₂ WR₂ DL₂ DR₂ M₂ E₂ R₂ Z₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hA tail0
          injection tail0 with hWL tail1
          injection tail1 with hWR tail2
          injection tail2 with hDL tail3
          injection tail3 with hDR tail4
          injection tail4 with hM tail5
          injection tail5 with hE tail6
          injection tail6 with hR tail7
          injection tail7 with hZ tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hP tail11
          injection tail11 with hN _
          subst hA; subst hWL; subst hWR; subst hDL; subst hDR; subst hM
          subst hE; subst hR; subst hZ; subst hH; subst hC; subst hP; subst hN
          rfl

instance regularCauchySquareBHistCarrier : BHistCarrier RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySquareToEventFlow
  fromEventFlow := regularCauchySquareFromEventFlow

instance regularCauchySquareChapterTasteGate :
    ChapterTasteGate RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow x) =
      some x
    exact regularCauchySquare_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySquareToEventFlow_injective heq)

instance regularCauchySquareFieldFaithful : FieldFaithful RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchySquareFields
  field_faithful := regularCauchySquareFields_faithful

instance regularCauchySquareNontrivial : Nontrivial RegularCauchySquareUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySquareUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchySquareUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchySquareUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySquareChapterTasteGate

theorem RegularCauchySquareUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchySquareDecodeBHist (regularCauchySquareEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySquareUp,
        regularCauchySquareFromEventFlow (regularCauchySquareToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchySquareUp,
          regularCauchySquareToEventFlow x =
              regularCauchySquareToEventFlow y →
            x = y) ∧
          regularCauchySquareEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchySquare_decode_encode,
      regularCauchySquare_round_trip,
      by
        intro x y heq
        exact regularCauchySquareToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchySquareUp
