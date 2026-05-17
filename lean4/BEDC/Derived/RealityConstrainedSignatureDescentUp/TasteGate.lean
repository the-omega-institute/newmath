import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSignatureDescentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSignatureDescentUp : Type where
  | mk (S Q T W H C P N : BHist) : RealityConstrainedSignatureDescentUp
  deriving DecidableEq

def realityConstrainedSignatureDescentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSignatureDescentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSignatureDescentEncodeBHist h

def realityConstrainedSignatureDescentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSignatureDescentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSignatureDescentDecodeBHist tail)

private theorem realityConstrainedSignatureDescent_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedSignatureDescentDecodeBHist
        (realityConstrainedSignatureDescentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realityConstrainedSignatureDescent_mk_congr
    {S S' Q Q' T T' W W' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hQ : Q' = Q) (hT : T' = T) (hW : W' = W)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RealityConstrainedSignatureDescentUp.mk S' Q' T' W' H' C' P' N' =
      RealityConstrainedSignatureDescentUp.mk S Q T W H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hQ
  cases hT
  cases hW
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realityConstrainedSignatureDescentFields :
    RealityConstrainedSignatureDescentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureDescentUp.mk S Q T W H C P N => [S, Q, T, W, H, C, P, N]

def realityConstrainedSignatureDescentToEventFlow :
    RealityConstrainedSignatureDescentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realityConstrainedSignatureDescentFields x).map
      realityConstrainedSignatureDescentEncodeBHist

def realityConstrainedSignatureDescentFromEventFlow :
    EventFlow → Option RealityConstrainedSignatureDescentUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: Q :: T :: W :: H :: C :: P :: N :: [] =>
      some
        (RealityConstrainedSignatureDescentUp.mk
          (realityConstrainedSignatureDescentDecodeBHist S)
          (realityConstrainedSignatureDescentDecodeBHist Q)
          (realityConstrainedSignatureDescentDecodeBHist T)
          (realityConstrainedSignatureDescentDecodeBHist W)
          (realityConstrainedSignatureDescentDecodeBHist H)
          (realityConstrainedSignatureDescentDecodeBHist C)
          (realityConstrainedSignatureDescentDecodeBHist P)
          (realityConstrainedSignatureDescentDecodeBHist N))
  | _ => none

private theorem realityConstrainedSignatureDescent_round_trip :
    ∀ x : RealityConstrainedSignatureDescentUp,
      realityConstrainedSignatureDescentFromEventFlow
        (realityConstrainedSignatureDescentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q T W H C P N =>
      exact
        congrArg some
          (realityConstrainedSignatureDescent_mk_congr
            (realityConstrainedSignatureDescent_decode_encode_bhist S)
            (realityConstrainedSignatureDescent_decode_encode_bhist Q)
            (realityConstrainedSignatureDescent_decode_encode_bhist T)
            (realityConstrainedSignatureDescent_decode_encode_bhist W)
            (realityConstrainedSignatureDescent_decode_encode_bhist H)
            (realityConstrainedSignatureDescent_decode_encode_bhist C)
            (realityConstrainedSignatureDescent_decode_encode_bhist P)
            (realityConstrainedSignatureDescent_decode_encode_bhist N))

private theorem realityConstrainedSignatureDescentToEventFlow_injective
    {x y : RealityConstrainedSignatureDescentUp} :
    realityConstrainedSignatureDescentToEventFlow x =
      realityConstrainedSignatureDescentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSignatureDescentFromEventFlow
          (realityConstrainedSignatureDescentToEventFlow x) =
        realityConstrainedSignatureDescentFromEventFlow
          (realityConstrainedSignatureDescentToEventFlow y) :=
    congrArg realityConstrainedSignatureDescentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedSignatureDescent_round_trip x).symm
      (Eq.trans hread (realityConstrainedSignatureDescent_round_trip y)))

private theorem realityConstrainedSignatureDescent_field_faithful :
    ∀ x y : RealityConstrainedSignatureDescentUp,
      realityConstrainedSignatureDescentFields x =
        realityConstrainedSignatureDescentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S Q T W H C P N =>
      cases y with
      | mk S' Q' T' W' H' C' P' N' =>
          cases hfields
          rfl

instance realityConstrainedSignatureDescentBHistCarrier :
    BHistCarrier RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSignatureDescentToEventFlow
  fromEventFlow := realityConstrainedSignatureDescentFromEventFlow

instance realityConstrainedSignatureDescentChapterTasteGate :
    ChapterTasteGate RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSignatureDescentFromEventFlow
        (realityConstrainedSignatureDescentToEventFlow x) = some x
    exact realityConstrainedSignatureDescent_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSignatureDescentToEventFlow_injective heq)

instance realityConstrainedSignatureDescentFieldFaithful :
    FieldFaithful RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSignatureDescentFields
  field_faithful := realityConstrainedSignatureDescent_field_faithful

instance realityConstrainedSignatureDescentNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealityConstrainedSignatureDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSignatureDescentUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedSignatureDescentUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSignatureDescentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSignatureDescentChapterTasteGate

theorem RealityConstrainedSignatureDescentCarrier_namecert_obligations
    (R : RealityConstrainedSignatureDescentUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ S Q T W H C P N : BHist,
          R = RealityConstrainedSignatureDescentUp.mk S Q T W H C P N ∧
            hsame row H)
      (fun row : BHist =>
        ∃ S Q T W H C P N : BHist,
          R = RealityConstrainedSignatureDescentUp.mk S Q T W H C P N ∧
            hsame row H)
      (fun row : BHist =>
        ∃ S Q T W H C P N : BHist,
          R = RealityConstrainedSignatureDescentUp.mk S Q T W H C P N ∧
            hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases R with
  | mk S Q T W H C P N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro H ⟨S, Q, T, W, H, C, P, N, rfl, hsame_refl H⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other same
            exact hsame_symm same
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other same source
            have sameRow : hsame row H := by
              cases source with
              | intro S' source =>
                  cases source with
                  | intro Q' source =>
                      cases source with
                      | intro T' source =>
                          cases source with
                          | intro W' source =>
                              cases source with
                              | intro H' source =>
                                  cases source with
                                  | intro C' source =>
                                      cases source with
                                      | intro P' source =>
                                          cases source with
                                          | intro N' source =>
                                              cases source.left
                                              exact source.right
            exact
              ⟨S, Q, T, W, H, C, P, N, rfl,
                hsame_trans (hsame_symm same) sameRow⟩
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.RealityConstrainedSignatureDescentUp
