import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailModulusUp : Type where
  | mk (S Q T W D H C P N : BHist) : RegularCauchyTailModulusUp
  deriving DecidableEq

def regularCauchyTailModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailModulusEncodeBHist h

def regularCauchyTailModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailModulusDecodeBHist tail)

private theorem regularCauchyTailModulus_decode_encode :
    ∀ h : BHist,
      regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailModulusFields : RegularCauchyTailModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailModulusUp.mk S Q T W D H C P N => [S, Q, T, W, D, H, C, P, N]

def regularCauchyTailModulusToEventFlow : RegularCauchyTailModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailModulusFields x).map regularCauchyTailModulusEncodeBHist

def regularCauchyTailModulusFromEventFlow :
    EventFlow → Option RegularCauchyTailModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | Q :: restQ =>
          match restQ with
          | T :: restT =>
              match restT with
              | W :: restW =>
                  match restW with
                  | D :: restD =>
                      match restD with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (RegularCauchyTailModulusUp.mk
                                              (regularCauchyTailModulusDecodeBHist S)
                                              (regularCauchyTailModulusDecodeBHist Q)
                                              (regularCauchyTailModulusDecodeBHist T)
                                              (regularCauchyTailModulusDecodeBHist W)
                                              (regularCauchyTailModulusDecodeBHist D)
                                              (regularCauchyTailModulusDecodeBHist H)
                                              (regularCauchyTailModulusDecodeBHist C)
                                              (regularCauchyTailModulusDecodeBHist P)
                                              (regularCauchyTailModulusDecodeBHist N))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem regularCauchyTailModulus_mk_congr
    {S S' Q Q' T T' W W' D D' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hQ : Q' = Q) (hT : T' = T) (hW : W' = W)
    (hD : D' = D) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    RegularCauchyTailModulusUp.mk S' Q' T' W' D' H' C' P' N' =
      RegularCauchyTailModulusUp.mk S Q T W D H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hQ
  cases hT
  cases hW
  cases hD
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem regularCauchyTailModulus_round_trip :
    ∀ x : RegularCauchyTailModulusUp,
      regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q T W D H C P N =>
      exact
        congrArg some
          (regularCauchyTailModulus_mk_congr
            (regularCauchyTailModulus_decode_encode S)
            (regularCauchyTailModulus_decode_encode Q)
            (regularCauchyTailModulus_decode_encode T)
            (regularCauchyTailModulus_decode_encode W)
            (regularCauchyTailModulus_decode_encode D)
            (regularCauchyTailModulus_decode_encode H)
            (regularCauchyTailModulus_decode_encode C)
            (regularCauchyTailModulus_decode_encode P)
            (regularCauchyTailModulus_decode_encode N))

private theorem regularCauchyTailModulusToEventFlow_injective
    {x y : RegularCauchyTailModulusUp} :
    regularCauchyTailModulusToEventFlow x = regularCauchyTailModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow x) :=
        (regularCauchyTailModulus_round_trip x).symm
      _ =
          regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow y) :=
        congrArg regularCauchyTailModulusFromEventFlow hxy
      _ = some y := regularCauchyTailModulus_round_trip y
  exact Option.some.inj optionEq

private theorem regularCauchyTailModulus_field_faithful :
    ∀ x y : RegularCauchyTailModulusUp,
      regularCauchyTailModulusFields x = regularCauchyTailModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Q₁ T₁ W₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ T₂ W₂ D₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS t0
          injection t0 with hQ t1
          injection t1 with hT t2
          injection t2 with hW t3
          injection t3 with hD t4
          injection t4 with hH t5
          injection t5 with hC t6
          injection t6 with hP t7
          injection t7 with hN _
          subst hS
          subst hQ
          subst hT
          subst hW
          subst hD
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyTailModulusBHistCarrier :
    BHistCarrier RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailModulusToEventFlow
  fromEventFlow := regularCauchyTailModulusFromEventFlow

instance regularCauchyTailModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow x) =
        some x
    exact regularCauchyTailModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailModulusToEventFlow_injective heq)

instance regularCauchyTailModulusFieldFaithful :
    FieldFaithful RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailModulusFields
  field_faithful := regularCauchyTailModulus_field_faithful

instance regularCauchyTailModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailModulusChapterTasteGate

theorem RegularCauchyTailModulusUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailModulusUp,
        regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyTailModulusUp,
        regularCauchyTailModulusToEventFlow x = regularCauchyTailModulusToEventFlow y ->
          x = y) ∧
      regularCauchyTailModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · intro x
    cases x with
    | mk S Q T W D H C P N =>
        exact
          congrArg some
            (regularCauchyTailModulus_mk_congr
              (regularCauchyTailModulus_decode_encode S)
              (regularCauchyTailModulus_decode_encode Q)
              (regularCauchyTailModulus_decode_encode T)
              (regularCauchyTailModulus_decode_encode W)
              (regularCauchyTailModulus_decode_encode D)
              (regularCauchyTailModulus_decode_encode H)
              (regularCauchyTailModulus_decode_encode C)
              (regularCauchyTailModulus_decode_encode P)
              (regularCauchyTailModulus_decode_encode N))
  constructor
  · intro x y heq
    have optionEq : some x = some y := by
      calc
        some x =
            regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow x) :=
          (regularCauchyTailModulus_round_trip x).symm
        _ =
            regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow y) :=
          congrArg regularCauchyTailModulusFromEventFlow heq
        _ = some y := regularCauchyTailModulus_round_trip y
    exact Option.some.inj optionEq
  · rfl

end BEDC.Derived.RegularCauchyTailModulusUp
