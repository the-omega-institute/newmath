import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicBoundaryShadowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicBoundaryShadowUp : Type where
  | mk (D M B T Q Y F H C P N : BHist) : HyperbolicBoundaryShadowUp
  deriving DecidableEq

def hyperbolicBoundaryShadowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicBoundaryShadowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicBoundaryShadowEncodeBHist h

def hyperbolicBoundaryShadowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicBoundaryShadowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicBoundaryShadowDecodeBHist tail)

private theorem HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hyperbolicBoundaryShadowDecodeBHist
        (hyperbolicBoundaryShadowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_mk_congr
    {D D' M M' B B' T T' Q Q' Y Y' F F' H H' C C' P P' N N' : BHist}
    (hD : D' = D)
    (hM : M' = M)
    (hB : B' = B)
    (hT : T' = T)
    (hQ : Q' = Q)
    (hY : Y' = Y)
    (hF : F' = F)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    HyperbolicBoundaryShadowUp.mk D' M' B' T' Q' Y' F' H' C' P' N' =
      HyperbolicBoundaryShadowUp.mk D M B T Q Y F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hM
  cases hB
  cases hT
  cases hQ
  cases hY
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective
    {a b : BHist} :
    hyperbolicBoundaryShadowEncodeBHist a =
      hyperbolicBoundaryShadowEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  have hd :
      hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist a) =
        hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist b) :=
    congrArg hyperbolicBoundaryShadowDecodeBHist h
  exact Eq.trans
    (HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode a).symm
    (Eq.trans hd (HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode b))

def hyperbolicBoundaryShadowFields : HyperbolicBoundaryShadowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicBoundaryShadowUp.mk D M B T Q Y F H C P N =>
      [D, M, B, T, Q, Y, F, H, C, P, N]

def hyperbolicBoundaryShadowToEventFlow : HyperbolicBoundaryShadowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicBoundaryShadowFields x).map hyperbolicBoundaryShadowEncodeBHist

def hyperbolicBoundaryShadowFromEventFlow :
    EventFlow → Option HyperbolicBoundaryShadowUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: M :: B :: T :: Q :: Y :: F :: H :: C :: P :: N :: [] =>
      some
        (HyperbolicBoundaryShadowUp.mk
          (hyperbolicBoundaryShadowDecodeBHist D)
          (hyperbolicBoundaryShadowDecodeBHist M)
          (hyperbolicBoundaryShadowDecodeBHist B)
          (hyperbolicBoundaryShadowDecodeBHist T)
          (hyperbolicBoundaryShadowDecodeBHist Q)
          (hyperbolicBoundaryShadowDecodeBHist Y)
          (hyperbolicBoundaryShadowDecodeBHist F)
          (hyperbolicBoundaryShadowDecodeBHist H)
          (hyperbolicBoundaryShadowDecodeBHist C)
          (hyperbolicBoundaryShadowDecodeBHist P)
          (hyperbolicBoundaryShadowDecodeBHist N))
  | _ => none

private theorem HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicBoundaryShadowUp) :
    hyperbolicBoundaryShadowFromEventFlow
      (hyperbolicBoundaryShadowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D M B T Q Y F H C P N =>
      change
        some
          (HyperbolicBoundaryShadowUp.mk
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist D))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist M))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist B))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist T))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist Q))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist Y))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist F))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist H))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist C))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist P))
            (hyperbolicBoundaryShadowDecodeBHist (hyperbolicBoundaryShadowEncodeBHist N))) =
          some (HyperbolicBoundaryShadowUp.mk D M B T Q Y F H C P N)
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode D]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode M]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode B]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode T]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode Q]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode Y]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode F]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode H]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode C]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode P]
      rw [HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode N]

private theorem HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicBoundaryShadowUp} :
    hyperbolicBoundaryShadowToEventFlow x =
      hyperbolicBoundaryShadowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk D₁ M₁ B₁ T₁ Q₁ Y₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ M₂ B₂ T₂ Q₂ Y₂ F₂ H₂ C₂ P₂ N₂ =>
          injection heq with hD tailD
          injection tailD with hM tailM
          injection tailM with hB tailB
          injection tailB with hT tailT
          injection tailT with hQ tailQ
          injection tailQ with hY tailY
          injection tailY with hF tailF
          injection tailF with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hD
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hM
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hB
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hT
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hQ
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hY
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hF
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hH
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hC
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hP
          cases
            HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_encode_injective hN
          rfl

private theorem HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : HyperbolicBoundaryShadowUp,
      hyperbolicBoundaryShadowFields x = hyperbolicBoundaryShadowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ M₁ B₁ T₁ Q₁ Y₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ M₂ B₂ T₂ Q₂ Y₂ F₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance hyperbolicBoundaryShadowBHistCarrier :
    BHistCarrier HyperbolicBoundaryShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicBoundaryShadowToEventFlow
  fromEventFlow := hyperbolicBoundaryShadowFromEventFlow

instance hyperbolicBoundaryShadowChapterTasteGate :
    ChapterTasteGate HyperbolicBoundaryShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicBoundaryShadowFromEventFlow
        (hyperbolicBoundaryShadowToEventFlow x) = some x
    exact HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact
      hxy
        (HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hyperbolicBoundaryShadowFieldFaithful :
    FieldFaithful HyperbolicBoundaryShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicBoundaryShadowFields
  field_faithful := HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_field_faithful

instance hyperbolicBoundaryShadowNontrivial : Nontrivial HyperbolicBoundaryShadowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicBoundaryShadowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HyperbolicBoundaryShadowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicBoundaryShadowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicBoundaryShadowChapterTasteGate

theorem HyperbolicBoundaryShadowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        hyperbolicBoundaryShadowDecodeBHist
          (hyperbolicBoundaryShadowEncodeBHist h) = h) ∧
      (∀ x y : HyperbolicBoundaryShadowUp,
        hyperbolicBoundaryShadowFields x = hyperbolicBoundaryShadowFields y → x = y) ∧
        (∃ x y : HyperbolicBoundaryShadowUp, x ≠ y) ∧
              hyperbolicBoundaryShadowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_decode,
      HyperbolicBoundaryShadowTasteGate_single_carrier_alignment_field_faithful,
      ⟨HyperbolicBoundaryShadowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        HyperbolicBoundaryShadowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.HyperbolicBoundaryShadowUp
