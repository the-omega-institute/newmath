import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalEmpiricalClosureGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalEmpiricalClosureGateUp : Type where
  | mk (S F J O L H C P N : BHist) : LocalEmpiricalClosureGateUp
  deriving DecidableEq

def localEmpiricalClosureGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localEmpiricalClosureGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localEmpiricalClosureGateEncodeBHist h

def localEmpiricalClosureGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localEmpiricalClosureGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localEmpiricalClosureGateDecodeBHist tail)

private theorem localEmpiricalClosureGateDecode_encode_bhist :
    ∀ h : BHist,
      localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def localEmpiricalClosureGateFields : LocalEmpiricalClosureGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocalEmpiricalClosureGateUp.mk S F J O L H C P N => [S, F, J, O, L, H, C, P, N]

def localEmpiricalClosureGateToEventFlow : LocalEmpiricalClosureGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocalEmpiricalClosureGateUp.mk S F J O L H C P N =>
      [[BMark.b0],
        localEmpiricalClosureGateEncodeBHist S,
        [BMark.b1, BMark.b0],
        localEmpiricalClosureGateEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        localEmpiricalClosureGateEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localEmpiricalClosureGateEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localEmpiricalClosureGateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localEmpiricalClosureGateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localEmpiricalClosureGateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        localEmpiricalClosureGateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        localEmpiricalClosureGateEncodeBHist N]

private def localEmpiricalClosureGateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => localEmpiricalClosureGateRawAt n rest

private def localEmpiricalClosureGateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => localEmpiricalClosureGateLengthEq n rest

def localEmpiricalClosureGateFromEventFlow :
    EventFlow → Option LocalEmpiricalClosureGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match localEmpiricalClosureGateLengthEq 18 flow with
      | true =>
          some
            (LocalEmpiricalClosureGateUp.mk
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 1 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 3 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 5 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 7 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 9 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 11 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 13 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 15 flow))
              (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateRawAt 17 flow)))
      | false => none

private theorem localEmpiricalClosureGate_round_trip :
    ∀ x : LocalEmpiricalClosureGateUp,
      localEmpiricalClosureGateFromEventFlow
        (localEmpiricalClosureGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F J O L H C P N =>
      change
        some
          (LocalEmpiricalClosureGateUp.mk
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist S))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist F))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist J))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist O))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist L))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist H))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist C))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist P))
            (localEmpiricalClosureGateDecodeBHist (localEmpiricalClosureGateEncodeBHist N))) =
          some (LocalEmpiricalClosureGateUp.mk S F J O L H C P N)
      rw [localEmpiricalClosureGateDecode_encode_bhist S,
        localEmpiricalClosureGateDecode_encode_bhist F,
        localEmpiricalClosureGateDecode_encode_bhist J,
        localEmpiricalClosureGateDecode_encode_bhist O,
        localEmpiricalClosureGateDecode_encode_bhist L,
        localEmpiricalClosureGateDecode_encode_bhist H,
        localEmpiricalClosureGateDecode_encode_bhist C,
        localEmpiricalClosureGateDecode_encode_bhist P,
        localEmpiricalClosureGateDecode_encode_bhist N]

private theorem localEmpiricalClosureGateToEventFlow_injective
    {x y : LocalEmpiricalClosureGateUp} :
    localEmpiricalClosureGateToEventFlow x =
        localEmpiricalClosureGateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localEmpiricalClosureGateFromEventFlow
          (localEmpiricalClosureGateToEventFlow x) =
        localEmpiricalClosureGateFromEventFlow
          (localEmpiricalClosureGateToEventFlow y) :=
    congrArg localEmpiricalClosureGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localEmpiricalClosureGate_round_trip x).symm
      (Eq.trans hread (localEmpiricalClosureGate_round_trip y)))

private theorem localEmpiricalClosureGate_field_faithful :
    ∀ x y : LocalEmpiricalClosureGateUp,
      localEmpiricalClosureGateFields x = localEmpiricalClosureGateFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 F1 J1 O1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 F2 J2 O2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance localEmpiricalClosureGateBHistCarrier :
    BHistCarrier LocalEmpiricalClosureGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localEmpiricalClosureGateToEventFlow
  fromEventFlow := localEmpiricalClosureGateFromEventFlow

instance localEmpiricalClosureGateChapterTasteGate :
    ChapterTasteGate LocalEmpiricalClosureGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      localEmpiricalClosureGateFromEventFlow
        (localEmpiricalClosureGateToEventFlow x) = some x
    exact localEmpiricalClosureGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localEmpiricalClosureGateToEventFlow_injective heq)

instance localEmpiricalClosureGateFieldFaithful :
    FieldFaithful LocalEmpiricalClosureGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := localEmpiricalClosureGateFields
  field_faithful := localEmpiricalClosureGate_field_faithful

instance localEmpiricalClosureGateNontrivial :
    Nontrivial LocalEmpiricalClosureGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocalEmpiricalClosureGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocalEmpiricalClosureGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocalEmpiricalClosureGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  localEmpiricalClosureGateChapterTasteGate

theorem LocalEmpiricalClosureGateTasteGate_single_carrier_alignment :
    (localEmpiricalClosureGateDecodeBHist
        (localEmpiricalClosureGateEncodeBHist BHist.Empty) = BHist.Empty) ∧
      (localEmpiricalClosureGateEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1]) ∧
        (∀ h : BHist,
          localEmpiricalClosureGateDecodeBHist
              (localEmpiricalClosureGateEncodeBHist h) = h) ∧
          (∀ x : LocalEmpiricalClosureGateUp,
            localEmpiricalClosureGateFromEventFlow
              (localEmpiricalClosureGateToEventFlow x) = some x) ∧
            (∀ x y : LocalEmpiricalClosureGateUp,
              localEmpiricalClosureGateToEventFlow x =
                  localEmpiricalClosureGateToEventFlow y →
                x = y) ∧
              Nonempty (ChapterTasteGate LocalEmpiricalClosureGateUp) ∧
                Nonempty (FieldFaithful LocalEmpiricalClosureGateUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨rfl, rfl, localEmpiricalClosureGateDecode_encode_bhist,
      localEmpiricalClosureGate_round_trip,
      (fun _ _ heq => localEmpiricalClosureGateToEventFlow_injective heq),
      ⟨localEmpiricalClosureGateChapterTasteGate⟩,
      ⟨localEmpiricalClosureGateFieldFaithful⟩⟩

theorem LocalEmpiricalClosureGateCarrier_nonfinality {S F J O L H C P N : BHist} :
    let g := LocalEmpiricalClosureGateUp.mk S F J O L H C P N
    localEmpiricalClosureGateToEventFlow g =
        [[BMark.b0],
          localEmpiricalClosureGateEncodeBHist S,
          [BMark.b1, BMark.b0],
          localEmpiricalClosureGateEncodeBHist F,
          [BMark.b1, BMark.b1, BMark.b0],
          localEmpiricalClosureGateEncodeBHist J,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          localEmpiricalClosureGateEncodeBHist O,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          localEmpiricalClosureGateEncodeBHist L,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          localEmpiricalClosureGateEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          localEmpiricalClosureGateEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          localEmpiricalClosureGateEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          localEmpiricalClosureGateEncodeBHist N] ∧
      hsame J J ∧ hsame O O ∧ hsame L L ∧ Cont J O (append J O) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact hsame_refl J
    · constructor
      · exact hsame_refl O
      · constructor
        · exact hsame_refl L
        · rfl

theorem LocalEmpiricalClosureGateCarrier_namecert_obligations
    (G : LocalEmpiricalClosureGateUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ S F J O L H C P N : BHist,
          G = LocalEmpiricalClosureGateUp.mk S F J O L H C P N ∧ hsame row N)
      (fun row : BHist =>
        ∃ S F J O L H C P N : BHist,
          G = LocalEmpiricalClosureGateUp.mk S F J O L H C P N ∧
            (hsame row S ∨ hsame row F ∨ hsame row J ∨ hsame row O ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N))
      (fun row : BHist =>
        ∃ S F J O L H C P N : BHist,
          G = LocalEmpiricalClosureGateUp.mk S F J O L H C P N ∧ hsame row N ∧
            Cont J O (append J O))
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert Cont
  cases G with
  | mk S F J O L H C P N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro N ⟨S, F, J, O, L, H, C, P, N, rfl, hsame_refl N⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other sameRows source
            cases source with
            | intro S' source =>
                cases source with
                | intro F' source =>
                    cases source with
                    | intro J' source =>
                        cases source with
                        | intro O' source =>
                            cases source with
                            | intro L' source =>
                                cases source with
                                | intro H' source =>
                                    cases source with
                                    | intro C' source =>
                                        cases source with
                                        | intro P' source =>
                                            cases source with
                                            | intro N' source =>
                                                exact
                                                  ⟨S', F', J', O', L', H', C', P', N',
                                                    source.left,
                                                    hsame_trans (hsame_symm sameRows)
                                                      source.right⟩
        }
        pattern_sound := by
          intro row source
          cases source with
          | intro S' source =>
              cases source with
              | intro F' source =>
                  cases source with
                  | intro J' source =>
                      cases source with
                      | intro O' source =>
                          cases source with
                          | intro L' source =>
                              cases source with
                              | intro H' source =>
                                  cases source with
                                  | intro C' source =>
                                      cases source with
                                      | intro P' source =>
                                          cases source with
                                          | intro N' source =>
                                              exact
                                                ⟨S', F', J', O', L', H', C', P', N',
                                                  source.left,
                                                  Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr source.right)))))))⟩
        ledger_sound := by
          intro row source
          cases source with
          | intro S' source =>
              cases source with
              | intro F' source =>
                  cases source with
                  | intro J' source =>
                      cases source with
                      | intro O' source =>
                          cases source with
                          | intro L' source =>
                              cases source with
                              | intro H' source =>
                                  cases source with
                                  | intro C' source =>
                                      cases source with
                                      | intro P' source =>
                                          cases source with
                                          | intro N' source =>
                                              exact
                                                ⟨S', F', J', O', L', H', C', P', N',
                                                  source.left, source.right, rfl⟩
      }

end BEDC.Derived.LocalEmpiricalClosureGateUp
