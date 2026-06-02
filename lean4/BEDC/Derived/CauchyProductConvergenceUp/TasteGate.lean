import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductConvergenceUp : Type where
  | mk (A B P T R D W E H C Q N : BHist) : CauchyProductConvergenceUp
  deriving DecidableEq

def CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist h

def CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CauchyProductConvergenceTasteGate_single_carrier_alignment_fields :
    CauchyProductConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductConvergenceUp.mk A B P T R D W E H C Q N =>
      [A, B, P, T, R, D, W, E, H, C, Q, N]

def CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow :
    CauchyProductConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b0, BMark.b0, BMark.b1] ::
        (CauchyProductConvergenceTasteGate_single_carrier_alignment_fields x).map
          CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist

def CauchyProductConvergenceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyProductConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: A :: B :: P :: T :: R :: D :: W :: E :: H :: C :: Q :: N :: [] =>
      some
        (CauchyProductConvergenceUp.mk
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist A)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist B)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist P)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist T)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist R)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist D)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist W)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist E)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist H)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist C)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist Q)
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem CauchyProductConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyProductConvergenceUp,
      CauchyProductConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B P T R D W E H C Q N =>
      change
        some
          (CauchyProductConvergenceUp.mk
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist A))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist B))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist T))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist R))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist W))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist E))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist H))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist Q))
            (CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyProductConvergenceUp.mk A B P T R D W E H C Q N)
      rw [CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode A,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode B,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode T,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyProductConvergenceUp} :
    CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow x =
      CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyProductConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyProductConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyProductConvergenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyProductConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyProductConvergenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyProductConvergenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyProductConvergenceUp,
      CauchyProductConvergenceTasteGate_single_carrier_alignment_fields x =
        CauchyProductConvergenceTasteGate_single_carrier_alignment_fields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ P₁ T₁ R₁ D₁ W₁ E₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk A₂ B₂ P₂ T₂ R₂ D₂ W₂ E₂ H₂ C₂ Q₂ N₂ =>
          injection hfields with hA tail1
          injection tail1 with hB tail2
          injection tail2 with hP tail3
          injection tail3 with hT tail4
          injection tail4 with hR tail5
          injection tail5 with hD tail6
          injection tail6 with hW tail7
          injection tail7 with hE tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hQ tail11
          injection tail11 with hN _
          subst hA
          subst hB
          subst hP
          subst hT
          subst hR
          subst hD
          subst hW
          subst hE
          subst hH
          subst hC
          subst hQ
          subst hN
          rfl

instance cauchyProductConvergenceBHistCarrier :
    BHistCarrier CauchyProductConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyProductConvergenceTasteGate_single_carrier_alignment_fromEventFlow

instance cauchyProductConvergenceChapterTasteGate :
    ChapterTasteGate CauchyProductConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyProductConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyProductConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyProductConvergenceFieldFaithful :
    FieldFaithful CauchyProductConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyProductConvergenceTasteGate_single_carrier_alignment_fields
  field_faithful :=
    CauchyProductConvergenceTasteGate_single_carrier_alignment_fields_faithful

instance cauchyProductConvergenceNontrivial :
    Nontrivial CauchyProductConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CauchyProductConvergenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hA
        cases hA⟩

def taste_gate : ChapterTasteGate CauchyProductConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductConvergenceChapterTasteGate

theorem CauchyProductConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CauchyProductConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyProductConvergenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CauchyProductConvergenceTasteGate_single_carrier_alignment_fields
          (CauchyProductConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        CauchyProductConvergenceTasteGate_single_carrier_alignment_toEventFlow
            (CauchyProductConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b0, BMark.b0, BMark.b1], [], [], [], [], [], [], [], [],
            [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨CauchyProductConvergenceTasteGate_single_carrier_alignment_decode_encode, rfl, rfl⟩

end BEDC.Derived.CauchyProductConvergenceUp
