import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CellularSubstrateClassifierBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CellularSubstrateClassifierBoundaryUp : Type where
  | mk (L O G M A R H C P N : BHist) : CellularSubstrateClassifierBoundaryUp
  deriving DecidableEq

def cellularSubstrateClassifierBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cellularSubstrateClassifierBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cellularSubstrateClassifierBoundaryEncodeBHist h

def cellularSubstrateClassifierBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cellularSubstrateClassifierBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cellularSubstrateClassifierBoundaryDecodeBHist tail)

private theorem CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cellularSubstrateClassifierBoundaryDecodeBHist
        (cellularSubstrateClassifierBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_mk_congr
    {L L' O O' G G' M M' A A' R R' H H' C C' P P' N N' : BHist}
    (hL : L' = L)
    (hO : O' = O)
    (hG : G' = G)
    (hM : M' = M)
    (hA : A' = A)
    (hR : R' = R)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    CellularSubstrateClassifierBoundaryUp.mk L' O' G' M' A' R' H' C' P' N' =
      CellularSubstrateClassifierBoundaryUp.mk L O G M A R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hO
  cases hG
  cases hM
  cases hA
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective
    {a b : BHist} :
    cellularSubstrateClassifierBoundaryEncodeBHist a =
      cellularSubstrateClassifierBoundaryEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  have hd :
      cellularSubstrateClassifierBoundaryDecodeBHist
          (cellularSubstrateClassifierBoundaryEncodeBHist a) =
        cellularSubstrateClassifierBoundaryDecodeBHist
          (cellularSubstrateClassifierBoundaryEncodeBHist b) :=
    congrArg cellularSubstrateClassifierBoundaryDecodeBHist h
  exact Eq.trans
    (CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode a).symm
    (Eq.trans hd
      (CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode b))

def cellularSubstrateClassifierBoundaryFields :
    CellularSubstrateClassifierBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CellularSubstrateClassifierBoundaryUp.mk L O G M A R H C P N =>
      [L, O, G, M, A, R, H, C, P, N]

def cellularSubstrateClassifierBoundaryToEventFlow :
    CellularSubstrateClassifierBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cellularSubstrateClassifierBoundaryFields x).map
        cellularSubstrateClassifierBoundaryEncodeBHist

def cellularSubstrateClassifierBoundaryFromEventFlow :
    EventFlow → Option CellularSubstrateClassifierBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | L :: O :: G :: M :: A :: R :: H :: C :: P :: N :: [] =>
      some
        (CellularSubstrateClassifierBoundaryUp.mk
          (cellularSubstrateClassifierBoundaryDecodeBHist L)
          (cellularSubstrateClassifierBoundaryDecodeBHist O)
          (cellularSubstrateClassifierBoundaryDecodeBHist G)
          (cellularSubstrateClassifierBoundaryDecodeBHist M)
          (cellularSubstrateClassifierBoundaryDecodeBHist A)
          (cellularSubstrateClassifierBoundaryDecodeBHist R)
          (cellularSubstrateClassifierBoundaryDecodeBHist H)
          (cellularSubstrateClassifierBoundaryDecodeBHist C)
          (cellularSubstrateClassifierBoundaryDecodeBHist P)
          (cellularSubstrateClassifierBoundaryDecodeBHist N))
  | _ => none

private theorem CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : CellularSubstrateClassifierBoundaryUp) :
    cellularSubstrateClassifierBoundaryFromEventFlow
      (cellularSubstrateClassifierBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L O G M A R H C P N =>
      change
        some
          (CellularSubstrateClassifierBoundaryUp.mk
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist L))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist O))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist G))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist M))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist A))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist R))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist H))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist C))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist P))
            (cellularSubstrateClassifierBoundaryDecodeBHist
              (cellularSubstrateClassifierBoundaryEncodeBHist N))) =
          some (CellularSubstrateClassifierBoundaryUp.mk L O G M A R H C P N)
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode L]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode O]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode G]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode M]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode A]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode R]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode H]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode C]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode P]
      rw [CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CellularSubstrateClassifierBoundaryUp} :
    cellularSubstrateClassifierBoundaryToEventFlow x =
      cellularSubstrateClassifierBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk L₁ O₁ G₁ M₁ A₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ O₂ G₂ M₂ A₂ R₂ H₂ C₂ P₂ N₂ =>
          injection heq with hL tailL
          injection tailL with hO tailO
          injection tailO with hG tailG
          injection tailG with hM tailM
          injection tailM with hA tailA
          injection tailA with hR tailR
          injection tailR with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hL
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hO
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hG
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hM
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hA
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hR
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hH
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hC
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hP
          cases
            CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_encode_injective hN
          rfl

private theorem CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CellularSubstrateClassifierBoundaryUp,
      cellularSubstrateClassifierBoundaryFields x =
        cellularSubstrateClassifierBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ O₁ G₁ M₁ A₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ O₂ G₂ M₂ A₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cellularSubstrateClassifierBoundaryBHistCarrier :
    BHistCarrier CellularSubstrateClassifierBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cellularSubstrateClassifierBoundaryToEventFlow
  fromEventFlow := cellularSubstrateClassifierBoundaryFromEventFlow

instance cellularSubstrateClassifierBoundaryChapterTasteGate :
    ChapterTasteGate CellularSubstrateClassifierBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cellularSubstrateClassifierBoundaryFromEventFlow
        (cellularSubstrateClassifierBoundaryToEventFlow x) = some x
    exact
      CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact
      hxy
        (CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
          heq)

instance cellularSubstrateClassifierBoundaryFieldFaithful :
    FieldFaithful CellularSubstrateClassifierBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cellularSubstrateClassifierBoundaryFields
  field_faithful :=
    CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_field_faithful

instance cellularSubstrateClassifierBoundaryNontrivial :
    Nontrivial CellularSubstrateClassifierBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CellularSubstrateClassifierBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CellularSubstrateClassifierBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CellularSubstrateClassifierBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cellularSubstrateClassifierBoundaryChapterTasteGate

theorem CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cellularSubstrateClassifierBoundaryDecodeBHist
          (cellularSubstrateClassifierBoundaryEncodeBHist h) = h) ∧
      (∀ x y : CellularSubstrateClassifierBoundaryUp,
        cellularSubstrateClassifierBoundaryFields x =
          cellularSubstrateClassifierBoundaryFields y → x = y) ∧
        (∃ x y : CellularSubstrateClassifierBoundaryUp, x ≠ y) ∧
              cellularSubstrateClassifierBoundaryEncodeBHist BHist.Empty =
                ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_decode,
      CellularSubstrateClassifierBoundaryTasteGate_single_carrier_alignment_field_faithful,
      ⟨CellularSubstrateClassifierBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        CellularSubstrateClassifierBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.CellularSubstrateClassifierBoundaryUp
