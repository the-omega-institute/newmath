import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertifiedUseProcessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CertifiedUseProcessUp : Type where
  | mk (U R C L H K P N : BHist) : CertifiedUseProcessUp
  deriving DecidableEq

def certifiedUseProcessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: certifiedUseProcessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: certifiedUseProcessEncodeBHist h

def certifiedUseProcessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (certifiedUseProcessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (certifiedUseProcessDecodeBHist tail)

private theorem certifiedUseProcess_decode_encode_bhist :
    ∀ h : BHist, certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def certifiedUseProcessFields : CertifiedUseProcessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CertifiedUseProcessUp.mk U R C L H K P N => [U, R, C, L, H, K, P, N]

def certifiedUseProcessToEventFlow : CertifiedUseProcessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map certifiedUseProcessEncodeBHist (certifiedUseProcessFields x)

def certifiedUseProcessFromEventFlow : EventFlow → Option CertifiedUseProcessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | C :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (CertifiedUseProcessUp.mk
                                          (certifiedUseProcessDecodeBHist U)
                                          (certifiedUseProcessDecodeBHist R)
                                          (certifiedUseProcessDecodeBHist C)
                                          (certifiedUseProcessDecodeBHist L)
                                          (certifiedUseProcessDecodeBHist H)
                                          (certifiedUseProcessDecodeBHist K)
                                          (certifiedUseProcessDecodeBHist P)
                                          (certifiedUseProcessDecodeBHist N))
                                  | _ :: _ => none

private theorem certifiedUseProcess_round_trip :
    ∀ x : CertifiedUseProcessUp,
      certifiedUseProcessFromEventFlow (certifiedUseProcessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U R C L H K P N =>
      change
        some
          (CertifiedUseProcessUp.mk
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist U))
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist R))
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist C))
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist L))
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist H))
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist K))
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist P))
            (certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist N))) =
          some (CertifiedUseProcessUp.mk U R C L H K P N)
      rw [certifiedUseProcess_decode_encode_bhist U,
        certifiedUseProcess_decode_encode_bhist R,
        certifiedUseProcess_decode_encode_bhist C,
        certifiedUseProcess_decode_encode_bhist L,
        certifiedUseProcess_decode_encode_bhist H,
        certifiedUseProcess_decode_encode_bhist K,
        certifiedUseProcess_decode_encode_bhist P,
        certifiedUseProcess_decode_encode_bhist N]

private theorem certifiedUseProcessToEventFlow_injective {x y : CertifiedUseProcessUp} :
    certifiedUseProcessToEventFlow x = certifiedUseProcessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      certifiedUseProcessFromEventFlow (certifiedUseProcessToEventFlow x) =
        certifiedUseProcessFromEventFlow (certifiedUseProcessToEventFlow y) :=
    congrArg certifiedUseProcessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (certifiedUseProcess_round_trip x).symm
      (Eq.trans hread (certifiedUseProcess_round_trip y)))

private theorem certifiedUseProcess_field_faithful :
    ∀ x y : CertifiedUseProcessUp,
      certifiedUseProcessFields x = certifiedUseProcessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk U₁ R₁ C₁ L₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk U₂ R₂ C₂ L₂ H₂ K₂ P₂ N₂ =>
          cases h
          rfl

instance certifiedUseProcessBHistCarrier : BHistCarrier CertifiedUseProcessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := certifiedUseProcessToEventFlow
  fromEventFlow := certifiedUseProcessFromEventFlow

instance certifiedUseProcessChapterTasteGate : ChapterTasteGate CertifiedUseProcessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change certifiedUseProcessFromEventFlow (certifiedUseProcessToEventFlow x) = some x
    exact certifiedUseProcess_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (certifiedUseProcessToEventFlow_injective heq)

instance certifiedUseProcessFieldFaithful : FieldFaithful CertifiedUseProcessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := certifiedUseProcessFields
  field_faithful := certifiedUseProcess_field_faithful

instance certifiedUseProcessNontrivial : Nontrivial CertifiedUseProcessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CertifiedUseProcessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CertifiedUseProcessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CertifiedUseProcessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  certifiedUseProcessChapterTasteGate

theorem CertifiedUseProcessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      certifiedUseProcessDecodeBHist (certifiedUseProcessEncodeBHist h) = h) ∧
      (∀ x : CertifiedUseProcessUp,
        certifiedUseProcessFromEventFlow (certifiedUseProcessToEventFlow x) = some x) ∧
        (∀ x y : CertifiedUseProcessUp,
          certifiedUseProcessToEventFlow x = certifiedUseProcessToEventFlow y → x = y) ∧
          (∀ x y : CertifiedUseProcessUp,
            certifiedUseProcessFields x = certifiedUseProcessFields y → x = y) ∧
            (∃ x y : CertifiedUseProcessUp, x ≠ y) ∧
              certifiedUseProcessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact certifiedUseProcess_decode_encode_bhist
  · constructor
    · exact certifiedUseProcess_round_trip
    · constructor
      · intro x y heq
        exact certifiedUseProcessToEventFlow_injective heq
      · constructor
        · exact certifiedUseProcess_field_faithful
        · constructor
          · exact
              ⟨CertifiedUseProcessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                CertifiedUseProcessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩
          · rfl

end BEDC.Derived.CertifiedUseProcessUp
