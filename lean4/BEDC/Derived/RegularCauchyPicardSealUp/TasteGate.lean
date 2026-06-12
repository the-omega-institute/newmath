import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyPicardSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyPicardSealUp : Type where
  | mk (I B M Q E H C P N : BHist) : RegularCauchyPicardSealUp
  deriving DecidableEq

def regularCauchyPicardSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyPicardSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyPicardSealEncodeBHist h

def regularCauchyPicardSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyPicardSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyPicardSealDecodeBHist tail)

private theorem RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyPicardSealDecodeBHist
          (regularCauchyPicardSealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem RegularCauchyPicardSealTasteGate_single_carrier_alignment_mk_congr
    {I₁ B₁ M₁ Q₁ E₁ H₁ C₁ P₁ N₁ I₂ B₂ M₂ Q₂ E₂ H₂ C₂ P₂ N₂ : BHist} :
    I₁ = I₂ →
      B₁ = B₂ →
        M₁ = M₂ →
          Q₁ = Q₂ →
            E₁ = E₂ →
              H₁ = H₂ →
                C₁ = C₂ →
                  P₁ = P₂ →
                    N₁ = N₂ →
                      RegularCauchyPicardSealUp.mk I₁ B₁ M₁ Q₁ E₁ H₁ C₁ P₁ N₁ =
                        RegularCauchyPicardSealUp.mk I₂ B₂ M₂ Q₂ E₂ H₂ C₂ P₂ N₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hI hB hM hQ hE hH hC hP hN
  cases hI
  cases hB
  cases hM
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyPicardSealFields : RegularCauchyPicardSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyPicardSealUp.mk I B M Q E H C P N => [I, B, M, Q, E, H, C, P, N]

def regularCauchyPicardSealToEventFlow : RegularCauchyPicardSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyPicardSealUp.mk I B M Q E H C P N =>
      [regularCauchyPicardSealEncodeBHist I,
        regularCauchyPicardSealEncodeBHist B,
        regularCauchyPicardSealEncodeBHist M,
        regularCauchyPicardSealEncodeBHist Q,
        regularCauchyPicardSealEncodeBHist E,
        regularCauchyPicardSealEncodeBHist H,
        regularCauchyPicardSealEncodeBHist C,
        regularCauchyPicardSealEncodeBHist P,
        regularCauchyPicardSealEncodeBHist N]

def regularCauchyPicardSealFromEventFlow : EventFlow → Option RegularCauchyPicardSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restB =>
      match restB with
      | [] => none
      | B :: restM =>
          match restM with
          | [] => none
          | M :: restQ =>
              match restQ with
              | [] => none
              | Q :: restE =>
                  match restE with
                  | [] => none
                  | E :: restH =>
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
                                            (RegularCauchyPicardSealUp.mk
                                              (regularCauchyPicardSealDecodeBHist I)
                                              (regularCauchyPicardSealDecodeBHist B)
                                              (regularCauchyPicardSealDecodeBHist M)
                                              (regularCauchyPicardSealDecodeBHist Q)
                                              (regularCauchyPicardSealDecodeBHist E)
                                              (regularCauchyPicardSealDecodeBHist H)
                                              (regularCauchyPicardSealDecodeBHist C)
                                              (regularCauchyPicardSealDecodeBHist P)
                                              (regularCauchyPicardSealDecodeBHist N))
                                      | _ :: _ => none

private theorem RegularCauchyPicardSealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyPicardSealUp,
      regularCauchyPicardSealFromEventFlow
          (regularCauchyPicardSealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B M Q E H C P N =>
      change
        some
          (RegularCauchyPicardSealUp.mk
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist I))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist B))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist M))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist Q))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist E))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist H))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist C))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist P))
            (regularCauchyPicardSealDecodeBHist
              (regularCauchyPicardSealEncodeBHist N))) =
          some (RegularCauchyPicardSealUp.mk I B M Q E H C P N)
      exact congrArg some
        (RegularCauchyPicardSealTasteGate_single_carrier_alignment_mk_congr
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode I)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode B)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode M)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode Q)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode E)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode H)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode C)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode P)
          (RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode N))

private theorem RegularCauchyPicardSealToEventFlow_injective
    {x y : RegularCauchyPicardSealUp} :
    regularCauchyPicardSealToEventFlow x = regularCauchyPicardSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyPicardSealFromEventFlow
          (regularCauchyPicardSealToEventFlow x) =
        regularCauchyPicardSealFromEventFlow
          (regularCauchyPicardSealToEventFlow y) :=
    congrArg regularCauchyPicardSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyPicardSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyPicardSealTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyPicardSealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyPicardSealUp,
      regularCauchyPicardSealFields x = regularCauchyPicardSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ B₁ M₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ B₂ M₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hI tail0
          injection tail0 with hB tail1
          injection tail1 with hM tail2
          injection tail2 with hQ tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hI
          subst hB
          subst hM
          subst hQ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyPicardSealBHistCarrier :
    BHistCarrier RegularCauchyPicardSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyPicardSealToEventFlow
  fromEventFlow := regularCauchyPicardSealFromEventFlow

instance regularCauchyPicardSealChapterTasteGate :
    ChapterTasteGate RegularCauchyPicardSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyPicardSealFromEventFlow
          (regularCauchyPicardSealToEventFlow x) =
        some x
    exact RegularCauchyPicardSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyPicardSealToEventFlow_injective heq)

instance regularCauchyPicardSealFieldFaithful :
    FieldFaithful RegularCauchyPicardSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyPicardSealFields
  field_faithful :=
    RegularCauchyPicardSealTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyPicardSealNontrivial : Nontrivial RegularCauchyPicardSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyPicardSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyPicardSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyPicardSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyPicardSealDecodeBHist
          (regularCauchyPicardSealEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyPicardSealUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyPicardSealUp) ∧
          regularCauchyPicardSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨RegularCauchyPicardSealTasteGate_single_carrier_alignment_decode,
      ⟨regularCauchyPicardSealBHistCarrier⟩,
      ⟨regularCauchyPicardSealChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyPicardSealUp
