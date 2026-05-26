import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailBasisUp : Type where
  | mk (T W D R E H C P N : BHist) : CauchyTailBasisUp
  deriving DecidableEq

def cauchyTailBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailBasisEncodeBHist h

def cauchyTailBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailBasisDecodeBHist tail)

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_mk_congr
    {T T' W W' D D' R R' E E' H H' C C' P P' N N' : BHist}
    (hT : T' = T)
    (hW : W' = W)
    (hD : D' = D)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    CauchyTailBasisUp.mk T' W' D' R' E' H' C' P' N' =
      CauchyTailBasisUp.mk T W D R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hW
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective
    {a b : BHist} :
    cauchyTailBasisEncodeBHist a = cauchyTailBasisEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  have hd :
      cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist a) =
        cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist b) :=
    congrArg cauchyTailBasisDecodeBHist h
  exact Eq.trans
    (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode a).symm
    (Eq.trans hd (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode b))

def cauchyTailBasisFields : CauchyTailBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailBasisUp.mk T W D R E H C P N => [T, W, D, R, E, H, C, P, N]

def cauchyTailBasisToEventFlow : CauchyTailBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailBasisFields x).map cauchyTailBasisEncodeBHist

def cauchyTailBasisFromEventFlow : EventFlow → Option CauchyTailBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CauchyTailBasisUp.mk
                                              (cauchyTailBasisDecodeBHist T)
                                              (cauchyTailBasisDecodeBHist W)
                                              (cauchyTailBasisDecodeBHist D)
                                              (cauchyTailBasisDecodeBHist R)
                                              (cauchyTailBasisDecodeBHist E)
                                              (cauchyTailBasisDecodeBHist H)
                                              (cauchyTailBasisDecodeBHist C)
                                              (cauchyTailBasisDecodeBHist P)
                                              (cauchyTailBasisDecodeBHist N))
                                      | _ :: _ => none

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_round_trip
    (x : CauchyTailBasisUp) :
    cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T W D R E H C P N =>
      change
        some
          (CauchyTailBasisUp.mk
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist T))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist W))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist D))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist R))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist E))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist H))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist C))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist P))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist N))) =
          some (CauchyTailBasisUp.mk T W D R E H C P N)
      exact
        congrArg some
          (CauchyTailBasisTasteGate_single_carrier_alignment_mk_congr
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode T)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode W)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode D)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode R)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode E)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode H)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode C)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode P)
            (CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode N))

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailBasisUp} :
    cauchyTailBasisToEventFlow x = cauchyTailBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk T₁ W₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ W₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection heq with hT tailT
          injection tailT with hW tailW
          injection tailW with hD tailD
          injection tailD with hR tailR
          injection tailR with hE tailE
          injection tailE with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hT
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hW
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hD
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hR
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hE
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hH
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hC
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hP
          cases CauchyTailBasisTasteGate_single_carrier_alignment_encode_injective hN
          rfl

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyTailBasisUp,
      cauchyTailBasisFields x = cauchyTailBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ W₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ W₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyTailBasisBHistCarrier : BHistCarrier CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailBasisToEventFlow
  fromEventFlow := cauchyTailBasisFromEventFlow

instance cauchyTailBasisChapterTasteGate : ChapterTasteGate CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) = some x
    exact CauchyTailBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyTailBasisFieldFaithful : FieldFaithful CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailBasisFields
  field_faithful := CauchyTailBasisTasteGate_single_carrier_alignment_field_faithful

instance cauchyTailBasisNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailBasisUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyTailBasisTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyTailBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailBasisChapterTasteGate

theorem CauchyTailBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist h) = h) ∧
      (∀ x : CauchyTailBasisUp,
        cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) = some x) ∧
      (∀ x y : CauchyTailBasisUp,
        cauchyTailBasisToEventFlow x = cauchyTailBasisToEventFlow y → x = y) ∧
      cauchyTailBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode,
      CauchyTailBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyTailBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

namespace TasteGate

theorem CauchyTailBasisTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyTailBasisUp) ∧
      Nonempty (FieldFaithful CauchyTailBasisUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyTailBasisUp) ∧
          (∀ h : BHist, cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist h) = h) ∧
            (∀ x : CauchyTailBasisUp,
              cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) = some x) ∧
              (∀ x y : CauchyTailBasisUp,
                cauchyTailBasisToEventFlow x = cauchyTailBasisToEventFlow y → x = y) ∧
                cauchyTailBasisEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyTailBasisChapterTasteGate⟩,
      ⟨cauchyTailBasisFieldFaithful⟩,
      ⟨cauchyTailBasisNontrivial⟩,
      CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode,
      CauchyTailBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyTailBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.CauchyTailBasisUp
