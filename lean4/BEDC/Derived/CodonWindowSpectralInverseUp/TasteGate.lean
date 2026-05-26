import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CodonWindowSpectralInverseUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CodonWindowSpectralInverseUp : Type where
  | mk (C A F H R T Q E K D P N : BHist) : CodonWindowSpectralInverseUp
  deriving DecidableEq

def codonWindowSpectralInverseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: codonWindowSpectralInverseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: codonWindowSpectralInverseEncodeBHist h

def codonWindowSpectralInverseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (codonWindowSpectralInverseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (codonWindowSpectralInverseDecodeBHist tail)

private theorem codonWindowSpectralInverse_decode_encode_bhist :
    ∀ h : BHist,
      codonWindowSpectralInverseDecodeBHist
        (codonWindowSpectralInverseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem codonWindowSpectralInverse_mk_congr
    {C C' A A' F F' H H' R R' T T' Q Q' E E' K K' D D' P P' N N' :
      BHist}
    (hC : C' = C) (hA : A' = A) (hF : F' = F) (hH : H' = H)
    (hR : R' = R) (hT : T' = T) (hQ : Q' = Q) (hE : E' = E)
    (hK : K' = K) (hD : D' = D) (hP : P' = P) (hN : N' = N) :
    CodonWindowSpectralInverseUp.mk C' A' F' H' R' T' Q' E' K' D' P' N' =
      CodonWindowSpectralInverseUp.mk C A F H R T Q E K D P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hA
  cases hF
  cases hH
  cases hR
  cases hT
  cases hQ
  cases hE
  cases hK
  cases hD
  cases hP
  cases hN
  rfl

def codonWindowSpectralInverseFields :
    CodonWindowSpectralInverseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CodonWindowSpectralInverseUp.mk C A F H R T Q E K D P N =>
      [C, A, F, H, R, T, Q, E, K, D, P, N]

def codonWindowSpectralInverseToEventFlow :
    CodonWindowSpectralInverseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (codonWindowSpectralInverseFields x).map
      codonWindowSpectralInverseEncodeBHist

private def codonWindowSpectralInverseRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => codonWindowSpectralInverseRawAt n rest

private def codonWindowSpectralInverseLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => codonWindowSpectralInverseLengthEq n rest

def codonWindowSpectralInverseFromEventFlow
    (flow : EventFlow) : Option CodonWindowSpectralInverseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match codonWindowSpectralInverseLengthEq 12 flow with
  | true =>
      some
        (CodonWindowSpectralInverseUp.mk
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 0 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 1 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 2 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 3 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 4 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 5 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 6 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 7 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 8 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 9 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 10 flow))
          (codonWindowSpectralInverseDecodeBHist
            (codonWindowSpectralInverseRawAt 11 flow)))
  | false => none

private theorem codonWindowSpectralInverse_round_trip :
    ∀ x : CodonWindowSpectralInverseUp,
      codonWindowSpectralInverseFromEventFlow
        (codonWindowSpectralInverseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C A F H R T Q E K D P N =>
      exact
        congrArg some
          (codonWindowSpectralInverse_mk_congr
            (codonWindowSpectralInverse_decode_encode_bhist C)
            (codonWindowSpectralInverse_decode_encode_bhist A)
            (codonWindowSpectralInverse_decode_encode_bhist F)
            (codonWindowSpectralInverse_decode_encode_bhist H)
            (codonWindowSpectralInverse_decode_encode_bhist R)
            (codonWindowSpectralInverse_decode_encode_bhist T)
            (codonWindowSpectralInverse_decode_encode_bhist Q)
            (codonWindowSpectralInverse_decode_encode_bhist E)
            (codonWindowSpectralInverse_decode_encode_bhist K)
            (codonWindowSpectralInverse_decode_encode_bhist D)
            (codonWindowSpectralInverse_decode_encode_bhist P)
            (codonWindowSpectralInverse_decode_encode_bhist N))

private theorem codonWindowSpectralInverseToEventFlow_injective
    {x y : CodonWindowSpectralInverseUp} :
    codonWindowSpectralInverseToEventFlow x =
      codonWindowSpectralInverseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      codonWindowSpectralInverseFromEventFlow
          (codonWindowSpectralInverseToEventFlow x) =
        codonWindowSpectralInverseFromEventFlow
          (codonWindowSpectralInverseToEventFlow y) :=
    congrArg codonWindowSpectralInverseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (codonWindowSpectralInverse_round_trip x).symm
      (Eq.trans hread (codonWindowSpectralInverse_round_trip y)))

private theorem codonWindowSpectralInverse_fields_faithful :
    ∀ x y : CodonWindowSpectralInverseUp,
      codonWindowSpectralInverseFields x = codonWindowSpectralInverseFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C₁ A₁ F₁ H₁ R₁ T₁ Q₁ E₁ K₁ D₁ P₁ N₁ =>
      cases y with
      | mk C₂ A₂ F₂ H₂ R₂ T₂ Q₂ E₂ K₂ D₂ P₂ N₂ =>
          injection hfields with hC tail0
          injection tail0 with hA tail1
          injection tail1 with hF tail2
          injection tail2 with hH tail3
          injection tail3 with hR tail4
          injection tail4 with hT tail5
          injection tail5 with hQ tail6
          injection tail6 with hE tail7
          injection tail7 with hK tail8
          injection tail8 with hD tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hC
          subst hA
          subst hF
          subst hH
          subst hR
          subst hT
          subst hQ
          subst hE
          subst hK
          subst hD
          subst hP
          subst hN
          rfl

instance codonWindowSpectralInverseBHistCarrier :
    BHistCarrier CodonWindowSpectralInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := codonWindowSpectralInverseToEventFlow
  fromEventFlow := codonWindowSpectralInverseFromEventFlow

instance codonWindowSpectralInverseChapterTasteGate :
    ChapterTasteGate CodonWindowSpectralInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      codonWindowSpectralInverseFromEventFlow
        (codonWindowSpectralInverseToEventFlow x) = some x
    exact codonWindowSpectralInverse_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (codonWindowSpectralInverseToEventFlow_injective heq)

instance codonWindowSpectralInverseFieldFaithful :
    FieldFaithful CodonWindowSpectralInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := codonWindowSpectralInverseFields
  field_faithful := codonWindowSpectralInverse_fields_faithful

instance codonWindowSpectralInverseNontrivial :
    Nontrivial CodonWindowSpectralInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CodonWindowSpectralInverseUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CodonWindowSpectralInverseUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CodonWindowSpectralInverseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  codonWindowSpectralInverseChapterTasteGate

theorem CodonWindowSpectralInverseTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      codonWindowSpectralInverseDecodeBHist
        (codonWindowSpectralInverseEncodeBHist h) = h) ∧
      (∀ x : CodonWindowSpectralInverseUp,
        codonWindowSpectralInverseFromEventFlow
          (codonWindowSpectralInverseToEventFlow x) = some x) ∧
        (∀ x y : CodonWindowSpectralInverseUp,
          codonWindowSpectralInverseToEventFlow x =
            codonWindowSpectralInverseToEventFlow y → x = y) ∧
          codonWindowSpectralInverseEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨codonWindowSpectralInverse_decode_encode_bhist,
      codonWindowSpectralInverse_round_trip,
      fun _ _ heq => codonWindowSpectralInverseToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CodonWindowSpectralInverseUp.TasteGate
