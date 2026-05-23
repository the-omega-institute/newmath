import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicGeometricTailUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicGeometricTailUp : Type where
  | mk (q n W D T R E H C P N : BHist) : DyadicGeometricTailUp
  deriving DecidableEq

def dyadicGeometricTailEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicGeometricTailEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicGeometricTailEncodeBHist h

def dyadicGeometricTailDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicGeometricTailDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicGeometricTailDecodeBHist tail)

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_mk_congr
    {q q' n n' W W' D D' T T' R R' E E' H H' C C' P P' N N' : BHist}
    (hq : q' = q)
    (hn : n' = n)
    (hW : W' = W)
    (hD : D' = D)
    (hT : T' = T)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    DyadicGeometricTailUp.mk q' n' W' D' T' R' E' H' C' P' N' =
      DyadicGeometricTailUp.mk q n W D T R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hq
  cases hn
  cases hW
  cases hD
  cases hT
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective
    {a b : BHist} :
    dyadicGeometricTailEncodeBHist a = dyadicGeometricTailEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  have hd :
      dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist a) =
        dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist b) :=
    congrArg dyadicGeometricTailDecodeBHist h
  exact Eq.trans
    (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode a).symm
    (Eq.trans hd (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode b))

def dyadicGeometricTailFields : DyadicGeometricTailUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicGeometricTailUp.mk q n W D T R E H C P N => [q, n, W, D, T, R, E, H, C, P, N]

def dyadicGeometricTailToEventFlow : DyadicGeometricTailUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicGeometricTailFields x).map dyadicGeometricTailEncodeBHist

def dyadicGeometricTailFromEventFlow : EventFlow → Option DyadicGeometricTailUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | q :: rest0 =>
      match rest0 with
      | [] => none
      | n :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (DyadicGeometricTailUp.mk
                                                      (dyadicGeometricTailDecodeBHist q)
                                                      (dyadicGeometricTailDecodeBHist n)
                                                      (dyadicGeometricTailDecodeBHist W)
                                                      (dyadicGeometricTailDecodeBHist D)
                                                      (dyadicGeometricTailDecodeBHist T)
                                                      (dyadicGeometricTailDecodeBHist R)
                                                      (dyadicGeometricTailDecodeBHist E)
                                                      (dyadicGeometricTailDecodeBHist H)
                                                      (dyadicGeometricTailDecodeBHist C)
                                                      (dyadicGeometricTailDecodeBHist P)
                                                      (dyadicGeometricTailDecodeBHist N))
                                              | _ :: _ => none

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip
    (x : DyadicGeometricTailUp) :
    dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk q n W D T R E H C P N =>
      change
        some
          (DyadicGeometricTailUp.mk
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist q))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist n))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist W))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist D))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist T))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist R))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist E))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist H))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist C))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist P))
            (dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist N))) =
          some (DyadicGeometricTailUp.mk q n W D T R E H C P N)
      exact
        congrArg some
          (DyadicGeometricTailTasteGate_single_carrier_alignment_mk_congr
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode q)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode n)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode W)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode D)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode T)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode R)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode E)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode H)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode C)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode P)
            (DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode N))

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicGeometricTailUp} :
    dyadicGeometricTailToEventFlow x = dyadicGeometricTailToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk q₁ n₁ W₁ D₁ T₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk q₂ n₂ W₂ D₂ T₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection heq with hq tailq
          injection tailq with hn tailn
          injection tailn with hW tailW
          injection tailW with hD tailD
          injection tailD with hT tailT
          injection tailT with hR tailR
          injection tailR with hE tailE
          injection tailE with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hq
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hn
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hW
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hD
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hT
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hR
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hE
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hH
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hC
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hP
          cases DyadicGeometricTailTasteGate_single_carrier_alignment_encode_injective hN
          rfl

private theorem DyadicGeometricTailTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DyadicGeometricTailUp,
      dyadicGeometricTailFields x = dyadicGeometricTailFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q₁ n₁ W₁ D₁ T₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk q₂ n₂ W₂ D₂ T₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicGeometricTailBHistCarrier : BHistCarrier DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicGeometricTailToEventFlow
  fromEventFlow := dyadicGeometricTailFromEventFlow

instance dyadicGeometricTailChapterTasteGate : ChapterTasteGate DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) = some x
    exact DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicGeometricTailTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicGeometricTailFieldFaithful : FieldFaithful DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicGeometricTailFields
  field_faithful := DyadicGeometricTailTasteGate_single_carrier_alignment_field_faithful

instance dyadicGeometricTailNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicGeometricTailUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicGeometricTailUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DyadicGeometricTailUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DyadicGeometricTailTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DyadicGeometricTailUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicGeometricTailChapterTasteGate

theorem DyadicGeometricTailTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist h) = h) ∧
      (∀ x : DyadicGeometricTailUp,
        dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) = some x) ∧
      (∀ x y : DyadicGeometricTailUp,
        dyadicGeometricTailToEventFlow x = dyadicGeometricTailToEventFlow y → x = y) ∧
      dyadicGeometricTailEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode,
      DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicGeometricTailTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

namespace TasteGate

theorem DyadicGeometricTailTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicGeometricTailUp) ∧
      Nonempty (FieldFaithful DyadicGeometricTailUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicGeometricTailUp) ∧
          (∀ h : BHist,
            dyadicGeometricTailDecodeBHist (dyadicGeometricTailEncodeBHist h) = h) ∧
            (∀ x : DyadicGeometricTailUp,
              dyadicGeometricTailFromEventFlow (dyadicGeometricTailToEventFlow x) =
                some x) ∧
              (∀ x y : DyadicGeometricTailUp,
                dyadicGeometricTailToEventFlow x = dyadicGeometricTailToEventFlow y →
                  x = y) ∧
                dyadicGeometricTailEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨dyadicGeometricTailChapterTasteGate⟩,
      ⟨dyadicGeometricTailFieldFaithful⟩,
      ⟨dyadicGeometricTailNontrivial⟩,
      DyadicGeometricTailTasteGate_single_carrier_alignment_decode_encode,
      DyadicGeometricTailTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicGeometricTailTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.DyadicGeometricTailUp
