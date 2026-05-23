import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionUp : Type where
  | mk (F D U E H C P N : BHist) : UniformCompletionUp
  deriving DecidableEq

def uniformCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionEncodeBHist h

def uniformCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionDecodeBHist tail)

private theorem uniformCompletionDecode_encode_bhist :
    ∀ h : BHist, uniformCompletionDecodeBHist (uniformCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionFields : UniformCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionUp.mk F D U E H C P N => [F, D, U, E, H, C, P, N]

def uniformCompletionToEventFlow : UniformCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformCompletionFields x).map uniformCompletionEncodeBHist

def uniformCompletionFromEventFlow : EventFlow → Option UniformCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: restD =>
      match restD with
      | [] => none
      | D :: restU =>
          match restU with
          | [] => none
          | U :: restE =>
              match restE with
              | [] => none
              | E :: restH =>
                  match restH with
                  | [] => none
                  | H :: restC =>
                      match restC with
                      | [] => none
                      | C :: restP =>
                          match restP with
                          | [] => none
                          | P :: restN =>
                              match restN with
                              | [] => none
                              | N :: rest =>
                                  match rest with
                                  | [] =>
                                      some
                                        (UniformCompletionUp.mk
                                          (uniformCompletionDecodeBHist F)
                                          (uniformCompletionDecodeBHist D)
                                          (uniformCompletionDecodeBHist U)
                                          (uniformCompletionDecodeBHist E)
                                          (uniformCompletionDecodeBHist H)
                                          (uniformCompletionDecodeBHist C)
                                          (uniformCompletionDecodeBHist P)
                                          (uniformCompletionDecodeBHist N))
                                  | _ :: _ => none

private theorem uniformCompletion_round_trip :
    ∀ x : UniformCompletionUp,
      uniformCompletionFromEventFlow (uniformCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F D U E H C P N =>
      change
        some
          (UniformCompletionUp.mk
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist F))
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist D))
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist U))
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist E))
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist H))
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist C))
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist P))
            (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist N))) =
          some (UniformCompletionUp.mk F D U E H C P N)
      rw [uniformCompletionDecode_encode_bhist F, uniformCompletionDecode_encode_bhist D,
        uniformCompletionDecode_encode_bhist U, uniformCompletionDecode_encode_bhist E,
        uniformCompletionDecode_encode_bhist H, uniformCompletionDecode_encode_bhist C,
        uniformCompletionDecode_encode_bhist P, uniformCompletionDecode_encode_bhist N]

private theorem uniformCompletionToEventFlow_injective {x y : UniformCompletionUp} :
    uniformCompletionToEventFlow x = uniformCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCompletionFromEventFlow (uniformCompletionToEventFlow x) =
        uniformCompletionFromEventFlow (uniformCompletionToEventFlow y) :=
    congrArg uniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCompletion_round_trip x).symm
      (Eq.trans hread (uniformCompletion_round_trip y)))

private theorem uniformCompletion_fields_faithful :
    ∀ x y : UniformCompletionUp, uniformCompletionFields x = uniformCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 D1 U1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 D2 U2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformCompletionBHistCarrier : BHistCarrier UniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionToEventFlow
  fromEventFlow := uniformCompletionFromEventFlow

instance uniformCompletionChapterTasteGate : ChapterTasteGate UniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCompletionFromEventFlow (uniformCompletionToEventFlow x) = some x
    exact uniformCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCompletionToEventFlow_injective heq)

instance uniformCompletionFieldFaithful : FieldFaithful UniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCompletionFields
  field_faithful := uniformCompletion_fields_faithful

instance uniformCompletionNontrivial : Nontrivial UniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompletionChapterTasteGate

namespace TasteGate

def UniformCompletionCarrier (row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  ∃ F D U E H C P N : BHist,
    hsame row N ∧ Cont F D U ∧ Cont U E H ∧ Cont H C P ∧ Cont P BHist.Empty N

def UniformCompletionCauchyFilterPattern (row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  ∃ F D U : BHist,
    Cont F D U ∧
      ∃ E H C P N : BHist,
        hsame row N ∧ Cont U E H ∧ Cont H C P ∧ Cont P BHist.Empty N

def UniformCompletionLedgerPolicy (row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  ∃ P N : BHist, hsame row N ∧ Cont P BHist.Empty N

def UniformCompletionClassifier (row row' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame NameCert
  hsame row row'

theorem UniformCompletionCarrier_namecert_obligation_surface :
    BEDC.FKernel.NameCert.SemanticNameCert UniformCompletionCarrier
      UniformCompletionCauchyFilterPattern UniformCompletionLedgerPolicy
      UniformCompletionClassifier := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert SemanticNameCert
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, hsame_refl BHist.Empty,
            cont_right_unit BHist.Empty, cont_right_unit BHist.Empty,
            cont_right_unit BHist.Empty, cont_right_unit BHist.Empty⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        obtain ⟨F, D, U, E, H, C, P, N, sameName, filterRoute, extensionRoute,
          replayRoute, ledgerRoute⟩ := source
        exact
          ⟨F, D, U, E, H, C, P, N, hsame_trans (hsame_symm sameRows) sameName,
            filterRoute, extensionRoute, replayRoute, ledgerRoute⟩
    }
    pattern_sound := by
      intro _row source
      obtain ⟨F, D, U, E, H, C, P, N, sameName, filterRoute, extensionRoute,
        replayRoute, ledgerRoute⟩ := source
      exact
        ⟨F, D, U, filterRoute, E, H, C, P, N, sameName, extensionRoute,
          replayRoute, ledgerRoute⟩
    ledger_sound := by
      intro _row source
      obtain ⟨_F, _D, _U, _E, _H, _C, P, N, sameName, _filterRoute,
        _extensionRoute, _replayRoute, ledgerRoute⟩ := source
      exact ⟨P, N, sameName, ledgerRoute⟩
  }

theorem UniformCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformCompletionUp) ∧
      Nonempty (FieldFaithful UniformCompletionUp) ∧
        Nonempty (Nontrivial UniformCompletionUp) ∧
          (∀ h : BHist, uniformCompletionDecodeBHist (uniformCompletionEncodeBHist h) = h) ∧
            (∀ x : UniformCompletionUp,
              uniformCompletionFromEventFlow (uniformCompletionToEventFlow x) = some x) ∧
              (∀ x y : UniformCompletionUp,
                uniformCompletionToEventFlow x = uniformCompletionToEventFlow y → x = y) ∧
                uniformCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨uniformCompletionChapterTasteGate⟩
  · constructor
    · exact ⟨uniformCompletionFieldFaithful⟩
    · constructor
      · exact ⟨uniformCompletionNontrivial⟩
      · constructor
        · exact uniformCompletionDecode_encode_bhist
        · constructor
          · exact uniformCompletion_round_trip
          · constructor
            · intro x y heq
              exact uniformCompletionToEventFlow_injective heq
            · rfl

theorem UniformCompletion_cauchy_filter_factorization {F D U E H C P N : BHist} :
    uniformCompletionFields (UniformCompletionUp.mk F D U E H C P N) =
        [F, D, U, E, H, C, P, N] ∧
      (Cont F D C →
        Cont (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist F))
          (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist D)) C) ∧
        hsame (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist F)) F ∧
          hsame (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist D)) D := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · rfl
  · constructor
    · intro route
      have hF := uniformCompletionDecode_encode_bhist F
      have hD := uniformCompletionDecode_encode_bhist D
      rw [hF, hD]
      exact route
    · constructor
      · exact uniformCompletionDecode_encode_bhist F
      · exact uniformCompletionDecode_encode_bhist D

theorem UniformCompletion_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {F D U E H C P N audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    uniformCompletionFields (UniformCompletionUp.mk F D U E H C P N) =
        [F, D, U, E, H, C, P, N] ∧
      Cont H C audit ∧ PkgSig bundle N pkg →
        hsame (uniformCompletionDecodeBHist (uniformCompletionEncodeBHist N)) N ∧
          Cont H C audit ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame ProbeBundle Pkg PkgSig
  intro surface
  exact
    ⟨uniformCompletionDecode_encode_bhist N,
      surface.right.left,
      surface.right.right⟩

theorem UniformCompletion_universal_extension_uniqueness
    {F D U E H C P N route route' : BHist} :
    UniformCompletionCarrier N →
      Cont U E route →
        Cont U E route' →
          hsame route H →
            hsame route' H →
              UniformCompletionClassifier route route' ∧
                UniformCompletionLedgerPolicy N ∧
                  UniformCompletionCauchyFilterPattern N := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  intro carrier routeLeft routeRight sameRoute sameRoute'
  obtain ⟨F0, D0, U0, E0, H0, C0, P0, N0, sameName, filterRoute,
    extensionRoute, replayRoute, ledgerRoute⟩ := carrier
  constructor
  · exact hsame_trans sameRoute (hsame_symm sameRoute')
  · constructor
    · exact ⟨P0, N0, sameName, ledgerRoute⟩
    · exact
        ⟨F0, D0, U0, filterRoute, E0, H0, C0, P0, N0, sameName,
          extensionRoute, replayRoute, ledgerRoute⟩

def taste_gate : ChapterTasteGate UniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.UniformCompletionUp.taste_gate

end TasteGate

end BEDC.Derived.UniformCompletionUp
