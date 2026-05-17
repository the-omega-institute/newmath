import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EpistemicWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EpistemicWitnessUp : Type where
  | mk (K A W H C P N : BHist) : EpistemicWitnessUp
  deriving DecidableEq

def epistemicWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: epistemicWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: epistemicWitnessEncodeBHist h

def epistemicWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (epistemicWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (epistemicWitnessDecodeBHist tail)

private theorem epistemicWitness_decode_encode_bhist :
    ∀ h : BHist,
      epistemicWitnessDecodeBHist (epistemicWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem epistemicWitness_mk_congr
    {K K' A A' W W' H H' C C' P P' N N' : BHist}
    (hK : K' = K) (hA : A' = A) (hW : W' = W) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    EpistemicWitnessUp.mk K' A' W' H' C' P' N' =
      EpistemicWitnessUp.mk K A W H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hA
  cases hW
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def epistemicWitnessFields : EpistemicWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EpistemicWitnessUp.mk K A W H C P N => [K, A, W, H, C, P, N]

def epistemicWitnessToEventFlow : EpistemicWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (epistemicWitnessFields x).map epistemicWitnessEncodeBHist

def epistemicWitnessFromEventFlow : EventFlow → Option EpistemicWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: A :: W :: H :: C :: P :: N :: [] =>
      some
        (EpistemicWitnessUp.mk
          (epistemicWitnessDecodeBHist K)
          (epistemicWitnessDecodeBHist A)
          (epistemicWitnessDecodeBHist W)
          (epistemicWitnessDecodeBHist H)
          (epistemicWitnessDecodeBHist C)
          (epistemicWitnessDecodeBHist P)
          (epistemicWitnessDecodeBHist N))
  | _ => none

private theorem epistemicWitness_round_trip :
    ∀ x : EpistemicWitnessUp,
      epistemicWitnessFromEventFlow (epistemicWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K A W H C P N =>
      exact
        congrArg some
          (epistemicWitness_mk_congr
            (epistemicWitness_decode_encode_bhist K)
            (epistemicWitness_decode_encode_bhist A)
            (epistemicWitness_decode_encode_bhist W)
            (epistemicWitness_decode_encode_bhist H)
            (epistemicWitness_decode_encode_bhist C)
            (epistemicWitness_decode_encode_bhist P)
            (epistemicWitness_decode_encode_bhist N))

private theorem epistemicWitnessToEventFlow_injective
    {x y : EpistemicWitnessUp} :
    epistemicWitnessToEventFlow x = epistemicWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      epistemicWitnessFromEventFlow (epistemicWitnessToEventFlow x) =
        epistemicWitnessFromEventFlow (epistemicWitnessToEventFlow y) :=
    congrArg epistemicWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (epistemicWitness_round_trip x).symm
      (Eq.trans hread (epistemicWitness_round_trip y)))

private theorem epistemicWitness_field_faithful :
    ∀ x y : EpistemicWitnessUp,
      epistemicWitnessFields x = epistemicWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K A W H C P N =>
      cases y with
      | mk K' A' W' H' C' P' N' =>
          cases hfields
          rfl

instance epistemicWitnessBHistCarrier : BHistCarrier EpistemicWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := epistemicWitnessToEventFlow
  fromEventFlow := epistemicWitnessFromEventFlow

instance epistemicWitnessChapterTasteGate :
    ChapterTasteGate EpistemicWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change epistemicWitnessFromEventFlow (epistemicWitnessToEventFlow x) = some x
    exact epistemicWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (epistemicWitnessToEventFlow_injective heq)

instance epistemicWitnessFieldFaithful : FieldFaithful EpistemicWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := epistemicWitnessFields
  field_faithful := epistemicWitness_field_faithful

instance epistemicWitnessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EpistemicWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EpistemicWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      EpistemicWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EpistemicWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  epistemicWitnessChapterTasteGate

theorem EpistemicWitnessCarrier_namecert_obligations
    (E : EpistemicWitnessUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ K A W H C P N : BHist,
          E = EpistemicWitnessUp.mk K A W H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ K A W H C P N : BHist,
          E = EpistemicWitnessUp.mk K A W H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ K A W H C P N : BHist,
          E = EpistemicWitnessUp.mk K A W H C P N ∧ hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases E with
  | mk K A W H C P N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro H ⟨K, A, W, H, C, P, N, rfl, hsame_refl H⟩
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
              | intro K' source =>
                  cases source with
                  | intro A' source =>
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
              ⟨K, A, W, H, C, P, N, rfl,
                hsame_trans (hsame_symm same) sameRow⟩
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.EpistemicWitnessUp
