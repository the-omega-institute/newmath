import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreOsgoodUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreOsgoodUp : Type where
  | mk
      (W F S U Q R D E H C P N : BHist) :
      MooreOsgoodUp
  deriving DecidableEq

def mooreOsgoodEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreOsgoodEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreOsgoodEncodeBHist h

def mooreOsgoodDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreOsgoodDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreOsgoodDecodeBHist tail)

private theorem MooreOsgoodTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem mooreOsgood_mk_congr
    {W₁ W₂ F₁ F₂ S₁ S₂ U₁ U₂ Q₁ Q₂ R₁ R₂ D₁ D₂ E₁ E₂ H₁ H₂ C₁ C₂ P₁ P₂
      N₁ N₂ : BHist} :
    W₁ = W₂ → F₁ = F₂ → S₁ = S₂ → U₁ = U₂ → Q₁ = Q₂ → R₁ = R₂ →
      D₁ = D₂ → E₁ = E₂ → H₁ = H₂ → C₁ = C₂ → P₁ = P₂ → N₁ = N₂ →
        MooreOsgoodUp.mk W₁ F₁ S₁ U₁ Q₁ R₁ D₁ E₁ H₁ C₁ P₁ N₁ =
          MooreOsgoodUp.mk W₂ F₂ S₂ U₂ Q₂ R₂ D₂ E₂ H₂ C₂ P₂ N₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hW hF hS hU hQ hR hD hE hH hC hP hN
  cases hW
  cases hF
  cases hS
  cases hU
  cases hQ
  cases hR
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def mooreOsgoodToEventFlow : MooreOsgoodUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MooreOsgoodUp.mk W F S U Q R D E H C P N =>
      [[BMark.b1, BMark.b0, BMark.b0, BMark.b1],
        mooreOsgoodEncodeBHist W,
        mooreOsgoodEncodeBHist F,
        mooreOsgoodEncodeBHist S,
        mooreOsgoodEncodeBHist U,
        mooreOsgoodEncodeBHist Q,
        mooreOsgoodEncodeBHist R,
        mooreOsgoodEncodeBHist D,
        mooreOsgoodEncodeBHist E,
        mooreOsgoodEncodeBHist H,
        mooreOsgoodEncodeBHist C,
        mooreOsgoodEncodeBHist P,
        mooreOsgoodEncodeBHist N]

def mooreOsgoodFromEventFlow : EventFlow → Option MooreOsgoodUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restW =>
      match restW with
      | [] => none
      | W :: restF =>
          match restF with
          | [] => none
          | F :: restS =>
              match restS with
              | [] => none
              | S :: restU =>
                  match restU with
                  | [] => none
                  | U :: restQ =>
                      match restQ with
                      | [] => none
                      | Q :: restR =>
                          match restR with
                          | [] => none
                          | R :: restD =>
                              match restD with
                              | [] => none
                              | D :: restE =>
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
                                                            (MooreOsgoodUp.mk
                                                              (mooreOsgoodDecodeBHist W)
                                                              (mooreOsgoodDecodeBHist F)
                                                              (mooreOsgoodDecodeBHist S)
                                                              (mooreOsgoodDecodeBHist U)
                                                              (mooreOsgoodDecodeBHist Q)
                                                              (mooreOsgoodDecodeBHist R)
                                                              (mooreOsgoodDecodeBHist D)
                                                              (mooreOsgoodDecodeBHist E)
                                                              (mooreOsgoodDecodeBHist H)
                                                              (mooreOsgoodDecodeBHist C)
                                                              (mooreOsgoodDecodeBHist P)
                                                              (mooreOsgoodDecodeBHist N))
                                                      | _ :: _ => none

private theorem MooreOsgoodTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MooreOsgoodUp, mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W F S U Q R D E H C P N =>
      change
        some
          (MooreOsgoodUp.mk
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist W))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist F))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist S))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist U))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist Q))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist R))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist D))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist E))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist H))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist C))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist P))
            (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist N))) =
          some (MooreOsgoodUp.mk W F S U Q R D E H C P N)
      exact
        congrArg some
          (mooreOsgood_mk_congr
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode W)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode F)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode S)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode U)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode Q)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode R)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode D)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode E)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode H)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode C)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode P)
            (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode N))

private theorem MooreOsgoodTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MooreOsgoodUp} :
    mooreOsgoodToEventFlow x = mooreOsgoodToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow x) =
        mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow y) :=
    congrArg mooreOsgoodFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MooreOsgoodTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MooreOsgoodTasteGate_single_carrier_alignment_round_trip y)))

instance mooreOsgoodBHistCarrier : BHistCarrier MooreOsgoodUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreOsgoodToEventFlow
  fromEventFlow := mooreOsgoodFromEventFlow

instance mooreOsgoodChapterTasteGate : ChapterTasteGate MooreOsgoodUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow x) = some x
    exact MooreOsgoodTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MooreOsgoodTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MooreOsgoodTasteGate_single_carrier_alignment :
    (∀ h : BHist, mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist h) = h) ∧
      (∀ x : MooreOsgoodUp,
        mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow x) = some x) ∧
        (∀ x y : MooreOsgoodUp,
          mooreOsgoodToEventFlow x = mooreOsgoodToEventFlow y → x = y) ∧
          mooreOsgoodEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk W F S U Q R D E H C P N =>
          change
            some
              (MooreOsgoodUp.mk
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist W))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist F))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist S))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist U))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist Q))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist R))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist D))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist E))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist H))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist C))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist P))
                (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist N))) =
              some (MooreOsgoodUp.mk W F S U Q R D E H C P N)
          exact
            congrArg some
              (mooreOsgood_mk_congr
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode W)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode F)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode S)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode U)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode Q)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode R)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode D)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode E)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode H)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode C)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode P)
                (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode N))
    · constructor
      · intro x y heq
        have hread :
            mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow x) =
              mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow y) :=
          congrArg mooreOsgoodFromEventFlow heq
        have hx :
            mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow x) = some x := by
          cases x with
          | mk W F S U Q R D E H C P N =>
              change
                some
                  (MooreOsgoodUp.mk
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist W))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist F))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist S))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist U))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist Q))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist R))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist D))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist E))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist H))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist C))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist P))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist N))) =
                  some (MooreOsgoodUp.mk W F S U Q R D E H C P N)
              exact
                congrArg some
                  (mooreOsgood_mk_congr
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode W)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode F)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode S)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode U)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode Q)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode R)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode D)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode E)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode H)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode C)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode P)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode N))
        have hy :
            mooreOsgoodFromEventFlow (mooreOsgoodToEventFlow y) = some y := by
          cases y with
          | mk W F S U Q R D E H C P N =>
              change
                some
                  (MooreOsgoodUp.mk
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist W))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist F))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist S))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist U))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist Q))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist R))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist D))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist E))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist H))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist C))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist P))
                    (mooreOsgoodDecodeBHist (mooreOsgoodEncodeBHist N))) =
                  some (MooreOsgoodUp.mk W F S U Q R D E H C P N)
              exact
                congrArg some
                  (mooreOsgood_mk_congr
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode W)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode F)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode S)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode U)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode Q)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode R)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode D)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode E)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode H)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode C)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode P)
                    (MooreOsgoodTasteGate_single_carrier_alignment_decode_encode N))
        exact Option.some.inj (Eq.trans hx.symm (Eq.trans hread hy))
      · rfl

end BEDC.Derived.MooreOsgoodUp
