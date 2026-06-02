import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCauchyApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCauchyApproximationUp : Type where
  | mk (D W Q E L H C P N : BHist) : DyadicCauchyApproximationUp
  deriving DecidableEq

def dyadicCauchyApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCauchyApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCauchyApproximationEncodeBHist h

def dyadicCauchyApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCauchyApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCauchyApproximationDecodeBHist tail)

private theorem DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicCauchyApproximationDecodeBHist
        (dyadicCauchyApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem dyadicCauchyApproximation_mk_congr
    {D D' W W' Q Q' E E' L L' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hW : W' = W) (hQ : Q' = Q) (hE : E' = E)
    (hL : L' = L) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    DyadicCauchyApproximationUp.mk D' W' Q' E' L' H' C' P' N' =
      DyadicCauchyApproximationUp.mk D W Q E L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hW
  cases hQ
  cases hE
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def dyadicCauchyApproximationFields :
    DyadicCauchyApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCauchyApproximationUp.mk D W Q E L H C P N => [D, W, Q, E, L, H, C, P, N]

def dyadicCauchyApproximationToEventFlow :
    DyadicCauchyApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCauchyApproximationFields x).map dyadicCauchyApproximationEncodeBHist

def dyadicCauchyApproximationFromEventFlow :
    EventFlow → Option DyadicCauchyApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest =>
      match rest with
      | [] => none
      | W :: rest =>
          match rest with
          | [] => none
          | Q :: rest =>
              match rest with
              | [] => none
              | E :: rest =>
                  match rest with
                  | [] => none
                  | L :: rest =>
                      match rest with
                      | [] => none
                      | H :: rest =>
                          match rest with
                          | [] => none
                          | C :: rest =>
                              match rest with
                              | [] => none
                              | P :: rest =>
                                  match rest with
                                  | [] => none
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (DyadicCauchyApproximationUp.mk
                                              (dyadicCauchyApproximationDecodeBHist D)
                                              (dyadicCauchyApproximationDecodeBHist W)
                                              (dyadicCauchyApproximationDecodeBHist Q)
                                              (dyadicCauchyApproximationDecodeBHist E)
                                              (dyadicCauchyApproximationDecodeBHist L)
                                              (dyadicCauchyApproximationDecodeBHist H)
                                              (dyadicCauchyApproximationDecodeBHist C)
                                              (dyadicCauchyApproximationDecodeBHist P)
                                              (dyadicCauchyApproximationDecodeBHist N))
                                      | _ :: _ => none

private theorem DyadicCauchyApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicCauchyApproximationUp,
      dyadicCauchyApproximationFromEventFlow (dyadicCauchyApproximationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q E L H C P N =>
      exact
        congrArg some
          (dyadicCauchyApproximation_mk_congr
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode D)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode W)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode Q)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode E)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode L)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode H)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode C)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode P)
            (DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode N))

private theorem dyadicCauchyApproximationToEventFlow_injective
    {x y : DyadicCauchyApproximationUp} :
    dyadicCauchyApproximationToEventFlow x =
      dyadicCauchyApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCauchyApproximationFromEventFlow (dyadicCauchyApproximationToEventFlow x) =
        dyadicCauchyApproximationFromEventFlow (dyadicCauchyApproximationToEventFlow y) :=
    congrArg dyadicCauchyApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicCauchyApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicCauchyApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem dyadicCauchyApproximation_field_faithful :
    ∀ x y : DyadicCauchyApproximationUp,
      dyadicCauchyApproximationFields x = dyadicCauchyApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ W₁ Q₁ E₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ Q₂ E₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicCauchyApproximationBHistCarrier :
    BHistCarrier DyadicCauchyApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCauchyApproximationToEventFlow
  fromEventFlow := dyadicCauchyApproximationFromEventFlow

instance dyadicCauchyApproximationChapterTasteGate :
    ChapterTasteGate DyadicCauchyApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicCauchyApproximationFromEventFlow
        (dyadicCauchyApproximationToEventFlow x) = some x
    exact DyadicCauchyApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicCauchyApproximationToEventFlow_injective heq)

instance dyadicCauchyApproximationFieldFaithful :
    FieldFaithful DyadicCauchyApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicCauchyApproximationFields
  field_faithful := dyadicCauchyApproximation_field_faithful

instance dyadicCauchyApproximationNontrivial :
    Nontrivial DyadicCauchyApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicCauchyApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicCauchyApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicCauchyApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicCauchyApproximationChapterTasteGate

theorem DyadicCauchyApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicCauchyApproximationUp) ∧
      Nonempty (FieldFaithful DyadicCauchyApproximationUp) ∧
      Nonempty (Nontrivial DyadicCauchyApproximationUp) ∧
      (∀ h : BHist,
        dyadicCauchyApproximationDecodeBHist
          (dyadicCauchyApproximationEncodeBHist h) = h) ∧
      (∀ x : DyadicCauchyApproximationUp,
        dyadicCauchyApproximationFromEventFlow
          (dyadicCauchyApproximationToEventFlow x) = some x) ∧
      (∀ x y : DyadicCauchyApproximationUp,
        dyadicCauchyApproximationToEventFlow x =
          dyadicCauchyApproximationToEventFlow y → x = y) ∧
      dyadicCauchyApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨dyadicCauchyApproximationChapterTasteGate⟩,
      ⟨dyadicCauchyApproximationFieldFaithful⟩,
      ⟨dyadicCauchyApproximationNontrivial⟩,
      DyadicCauchyApproximationTasteGate_single_carrier_alignment_decode,
      DyadicCauchyApproximationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => dyadicCauchyApproximationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicCauchyApproximationUp
