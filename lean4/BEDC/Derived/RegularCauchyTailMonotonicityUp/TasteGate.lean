import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailMonotonicityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailMonotonicityUp : Type where
  | mk (E L R D T A Q H C P N : BHist) : RegularCauchyTailMonotonicityUp
  deriving DecidableEq

def regularCauchyTailMonotonicityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailMonotonicityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailMonotonicityEncodeBHist h

def regularCauchyTailMonotonicityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailMonotonicityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailMonotonicityDecodeBHist tail)

private theorem regularCauchyTailMonotonicity_decode_encode :
    ∀ h : BHist,
      regularCauchyTailMonotonicityDecodeBHist
          (regularCauchyTailMonotonicityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailMonotonicityFields :
    RegularCauchyTailMonotonicityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailMonotonicityUp.mk E L R D T A Q H C P N =>
      [E, L, R, D, T, A, Q, H, C, P, N]

def regularCauchyTailMonotonicityToEventFlow :
    RegularCauchyTailMonotonicityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailMonotonicityUp.mk E L R D T A Q H C P N =>
      [regularCauchyTailMonotonicityEncodeBHist E,
        regularCauchyTailMonotonicityEncodeBHist L,
        regularCauchyTailMonotonicityEncodeBHist R,
        regularCauchyTailMonotonicityEncodeBHist D,
        regularCauchyTailMonotonicityEncodeBHist T,
        regularCauchyTailMonotonicityEncodeBHist A,
        regularCauchyTailMonotonicityEncodeBHist Q,
        regularCauchyTailMonotonicityEncodeBHist H,
        regularCauchyTailMonotonicityEncodeBHist C,
        regularCauchyTailMonotonicityEncodeBHist P,
        regularCauchyTailMonotonicityEncodeBHist N]

def regularCauchyTailMonotonicityFromEventFlow :
    EventFlow → Option RegularCauchyTailMonotonicityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: restL =>
      match restL with
      | [] => none
      | L :: restR =>
          match restR with
          | [] => none
          | R :: restD =>
              match restD with
              | [] => none
              | D :: restT =>
                  match restT with
                  | [] => none
                  | T :: restA =>
                      match restA with
                      | [] => none
                      | A :: restQ =>
                          match restQ with
                          | [] => none
                          | Q :: restH =>
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
                                                    (RegularCauchyTailMonotonicityUp.mk
                                                      (regularCauchyTailMonotonicityDecodeBHist E)
                                                      (regularCauchyTailMonotonicityDecodeBHist L)
                                                      (regularCauchyTailMonotonicityDecodeBHist R)
                                                      (regularCauchyTailMonotonicityDecodeBHist D)
                                                      (regularCauchyTailMonotonicityDecodeBHist T)
                                                      (regularCauchyTailMonotonicityDecodeBHist A)
                                                      (regularCauchyTailMonotonicityDecodeBHist Q)
                                                      (regularCauchyTailMonotonicityDecodeBHist H)
                                                      (regularCauchyTailMonotonicityDecodeBHist C)
                                                      (regularCauchyTailMonotonicityDecodeBHist P)
                                                      (regularCauchyTailMonotonicityDecodeBHist N))
                                              | _ :: _ => none

private theorem regularCauchyTailMonotonicity_round_trip :
    ∀ x : RegularCauchyTailMonotonicityUp,
      regularCauchyTailMonotonicityFromEventFlow
          (regularCauchyTailMonotonicityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E L R D T A Q H C P N =>
      change
        some
          (RegularCauchyTailMonotonicityUp.mk
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist E))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist L))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist R))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist D))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist T))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist A))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist Q))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist H))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist C))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist P))
            (regularCauchyTailMonotonicityDecodeBHist
              (regularCauchyTailMonotonicityEncodeBHist N))) =
          some (RegularCauchyTailMonotonicityUp.mk E L R D T A Q H C P N)
      rw [regularCauchyTailMonotonicity_decode_encode E,
        regularCauchyTailMonotonicity_decode_encode L,
        regularCauchyTailMonotonicity_decode_encode R,
        regularCauchyTailMonotonicity_decode_encode D,
        regularCauchyTailMonotonicity_decode_encode T,
        regularCauchyTailMonotonicity_decode_encode A,
        regularCauchyTailMonotonicity_decode_encode Q,
        regularCauchyTailMonotonicity_decode_encode H,
        regularCauchyTailMonotonicity_decode_encode C,
        regularCauchyTailMonotonicity_decode_encode P,
        regularCauchyTailMonotonicity_decode_encode N]

private theorem regularCauchyTailMonotonicityToEventFlow_injective
    {x y : RegularCauchyTailMonotonicityUp} :
    regularCauchyTailMonotonicityToEventFlow x =
        regularCauchyTailMonotonicityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk E₁ L₁ R₁ D₁ T₁ A₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ L₂ R₂ D₂ T₂ A₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection heq with hE tail0
          injection tail0 with hL tail1
          injection tail1 with hR tail2
          injection tail2 with hD tail3
          injection tail3 with hT tail4
          injection tail4 with hA tail5
          injection tail5 with hQ tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          have eE : E₁ = E₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode E₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hE)
                (regularCauchyTailMonotonicity_decode_encode E₂))
          have eL : L₁ = L₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode L₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hL)
                (regularCauchyTailMonotonicity_decode_encode L₂))
          have eR : R₁ = R₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode R₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hR)
                (regularCauchyTailMonotonicity_decode_encode R₂))
          have eD : D₁ = D₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode D₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hD)
                (regularCauchyTailMonotonicity_decode_encode D₂))
          have eT : T₁ = T₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode T₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hT)
                (regularCauchyTailMonotonicity_decode_encode T₂))
          have eA : A₁ = A₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode A₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hA)
                (regularCauchyTailMonotonicity_decode_encode A₂))
          have eQ : Q₁ = Q₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode Q₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hQ)
                (regularCauchyTailMonotonicity_decode_encode Q₂))
          have eH : H₁ = H₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode H₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hH)
                (regularCauchyTailMonotonicity_decode_encode H₂))
          have eC : C₁ = C₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode C₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hC)
                (regularCauchyTailMonotonicity_decode_encode C₂))
          have eP : P₁ = P₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode P₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hP)
                (regularCauchyTailMonotonicity_decode_encode P₂))
          have eN : N₁ = N₂ :=
            Eq.trans (regularCauchyTailMonotonicity_decode_encode N₁).symm
              (Eq.trans (congrArg regularCauchyTailMonotonicityDecodeBHist hN)
                (regularCauchyTailMonotonicity_decode_encode N₂))
          subst eE; subst eL; subst eR; subst eD; subst eT; subst eA
          subst eQ; subst eH; subst eC; subst eP; subst eN
          rfl

private theorem regularCauchyTailMonotonicityFields_faithful :
    ∀ x y : RegularCauchyTailMonotonicityUp,
      regularCauchyTailMonotonicityFields x =
          regularCauchyTailMonotonicityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ L₁ R₁ D₁ T₁ A₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ L₂ R₂ D₂ T₂ A₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hE tail0
          injection tail0 with hL tail1
          injection tail1 with hR tail2
          injection tail2 with hD tail3
          injection tail3 with hT tail4
          injection tail4 with hA tail5
          injection tail5 with hQ tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hE; subst hL; subst hR; subst hD; subst hT; subst hA
          subst hQ; subst hH; subst hC; subst hP; subst hN
          rfl

instance regularCauchyTailMonotonicityBHistCarrier :
    BHistCarrier RegularCauchyTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailMonotonicityToEventFlow
  fromEventFlow := regularCauchyTailMonotonicityFromEventFlow

instance regularCauchyTailMonotonicityChapterTasteGate :
    ChapterTasteGate RegularCauchyTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailMonotonicityFromEventFlow
          (regularCauchyTailMonotonicityToEventFlow x) =
        some x
    exact regularCauchyTailMonotonicity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailMonotonicityToEventFlow_injective heq)

instance regularCauchyTailMonotonicityFieldFaithful :
    FieldFaithful RegularCauchyTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailMonotonicityFields
  field_faithful := regularCauchyTailMonotonicityFields_faithful

instance regularCauchyTailMonotonicityNontrivial :
    Nontrivial RegularCauchyTailMonotonicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailMonotonicityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyTailMonotonicityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailMonotonicityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailMonotonicityChapterTasteGate

theorem RegularCauchyTailMonotonicityUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailMonotonicityDecodeBHist
          (regularCauchyTailMonotonicityEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyTailMonotonicityUp,
        regularCauchyTailMonotonicityFromEventFlow
            (regularCauchyTailMonotonicityToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyTailMonotonicityUp,
          regularCauchyTailMonotonicityToEventFlow x =
              regularCauchyTailMonotonicityToEventFlow y →
            x = y) ∧
          regularCauchyTailMonotonicityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyTailMonotonicity_decode_encode,
      regularCauchyTailMonotonicity_round_trip,
      by
        intro x y heq
        exact regularCauchyTailMonotonicityToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyTailMonotonicityUp
