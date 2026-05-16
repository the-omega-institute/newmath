import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DigestInscriptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DigestInscriptionUp : Type where
  | mk (D F G T S O H C P N : BHist) : DigestInscriptionUp
  deriving DecidableEq

def digestInscriptionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: digestInscriptionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: digestInscriptionEncodeBHist h

def digestInscriptionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (digestInscriptionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (digestInscriptionDecodeBHist tail)

theorem DigestInscriptionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, digestInscriptionDecodeBHist (digestInscriptionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem DigestInscriptionTasteGate_single_carrier_alignment_mk_congr
    {D D' F F' G G' T T' S S' O O' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hF : F' = F) (hG : G' = G) (hT : T' = T)
    (hS : S' = S) (hO : O' = O) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    DigestInscriptionUp.mk D' F' G' T' S' O' H' C' P' N' =
      DigestInscriptionUp.mk D F G T S O H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hF
  cases hG
  cases hT
  cases hS
  cases hO
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def digestInscriptionFields : DigestInscriptionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DigestInscriptionUp.mk D F G T S O H C P N => [D, F, G, T, S, O, H, C, P, N]

def digestInscriptionToEventFlow : DigestInscriptionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (digestInscriptionFields x).map digestInscriptionEncodeBHist

def digestInscriptionFromEventFlow : EventFlow → Option DigestInscriptionUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: F :: G :: T :: S :: O :: H :: C :: P :: N :: [] =>
      some
        (DigestInscriptionUp.mk
          (digestInscriptionDecodeBHist D)
          (digestInscriptionDecodeBHist F)
          (digestInscriptionDecodeBHist G)
          (digestInscriptionDecodeBHist T)
          (digestInscriptionDecodeBHist S)
          (digestInscriptionDecodeBHist O)
          (digestInscriptionDecodeBHist H)
          (digestInscriptionDecodeBHist C)
          (digestInscriptionDecodeBHist P)
          (digestInscriptionDecodeBHist N))
  | _ => none

private theorem digestInscription_round_trip :
    ∀ x : DigestInscriptionUp,
      digestInscriptionFromEventFlow (digestInscriptionToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | DigestInscriptionUp.mk D F G T S O H C P N =>
      congrArg some
        (DigestInscriptionTasteGate_single_carrier_alignment_mk_congr
          (DigestInscriptionTasteGate_single_carrier_alignment_decode D)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode F)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode G)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode T)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode S)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode O)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode H)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode C)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode P)
          (DigestInscriptionTasteGate_single_carrier_alignment_decode N))

private theorem digestInscriptionToEventFlow_injective {x y : DigestInscriptionUp} :
    digestInscriptionToEventFlow x = digestInscriptionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      digestInscriptionFromEventFlow (digestInscriptionToEventFlow x) =
        digestInscriptionFromEventFlow (digestInscriptionToEventFlow y) :=
    congrArg digestInscriptionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (digestInscription_round_trip x).symm
      (Eq.trans hread (digestInscription_round_trip y)))

private theorem digestInscription_fields_faithful :
    ∀ x y : DigestInscriptionUp,
      digestInscriptionFields x = digestInscriptionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D₁ F₁ G₁ T₁ S₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ F₂ G₂ T₂ S₂ O₂ H₂ C₂ P₂ N₂ =>
          injection h with hD t1
          injection t1 with hF t2
          injection t2 with hG t3
          injection t3 with hT t4
          injection t4 with hS t5
          injection t5 with hO t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hD
          cases hF
          cases hG
          cases hT
          cases hS
          cases hO
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance digestInscriptionBHistCarrier : BHistCarrier DigestInscriptionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := digestInscriptionToEventFlow
  fromEventFlow := digestInscriptionFromEventFlow

instance digestInscriptionChapterTasteGate : ChapterTasteGate DigestInscriptionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change digestInscriptionFromEventFlow (digestInscriptionToEventFlow x) = some x
    exact digestInscription_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (digestInscriptionToEventFlow_injective heq)

instance digestInscriptionFieldFaithful : FieldFaithful DigestInscriptionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := digestInscriptionFields
  field_faithful := digestInscription_fields_faithful

instance digestInscriptionNontrivial : Nontrivial DigestInscriptionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DigestInscriptionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DigestInscriptionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DigestInscriptionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  digestInscriptionChapterTasteGate

theorem DigestInscriptionTasteGate_single_carrier_alignment :
    (∀ h : BHist, digestInscriptionDecodeBHist (digestInscriptionEncodeBHist h) = h) ∧
      (∀ D F G T S O H C P N : BHist,
        digestInscriptionFields (DigestInscriptionUp.mk D F G T S O H C P N) =
          [D, F, G, T, S, O, H, C, P, N]) ∧
        (∀ D F G T S O H C P N D' F' G' T' S' O' H' C' P' N' : BHist,
          [D, F, G, T, S, O, H, C, P, N] = [D', F', G', T', S', O', H', C', P', N'] →
            DigestInscriptionUp.mk D F G T S O H C P N =
              DigestInscriptionUp.mk D' F' G' T' S' O' H' C' P' N') ∧
          digestInscriptionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DigestInscriptionTasteGate_single_carrier_alignment_decode
  · constructor
    · intro D F G T S O H C P N
      rfl
    · constructor
      · intro D F G T S O H C P N D' F' G' T' S' O' H' C' P' N' h
        injection h with hD t1
        injection t1 with hF t2
        injection t2 with hG t3
        injection t3 with hT t4
        injection t4 with hS t5
        injection t5 with hO t6
        injection t6 with hH t7
        injection t7 with hC t8
        injection t8 with hP t9
        injection t9 with hN _
        exact
          DigestInscriptionTasteGate_single_carrier_alignment_mk_congr hD hF hG hT hS hO
            hH hC hP hN
      · rfl

end BEDC.Derived.DigestInscriptionUp
