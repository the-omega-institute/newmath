import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyUniformityUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyUniformityUp : Type where
  | mk (R W D E H C P N : BHist) : RegularCauchyUniformityUp
  deriving DecidableEq

def regularCauchyUniformityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyUniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyUniformityEncodeBHist h

def regularCauchyUniformityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyUniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyUniformityDecodeBHist tail)

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyUniformityFields : RegularCauchyUniformityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyUniformityUp.mk R W D E H C P N => [R, W, D, E, H, C, P, N]

def regularCauchyUniformityToEventFlow : RegularCauchyUniformityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyUniformityFields x).map regularCauchyUniformityEncodeBHist

def regularCauchyUniformityFromEventFlow : EventFlow -> Option RegularCauchyUniformityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (RegularCauchyUniformityUp.mk
                                          (regularCauchyUniformityDecodeBHist R)
                                          (regularCauchyUniformityDecodeBHist W)
                                          (regularCauchyUniformityDecodeBHist D)
                                          (regularCauchyUniformityDecodeBHist E)
                                          (regularCauchyUniformityDecodeBHist H)
                                          (regularCauchyUniformityDecodeBHist C)
                                          (regularCauchyUniformityDecodeBHist P)
                                          (regularCauchyUniformityDecodeBHist N))
                                  | _ :: _ => none

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyUniformityUp,
      regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D E H C P N =>
      change
        some
          (RegularCauchyUniformityUp.mk
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist R))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist W))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist D))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist E))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist H))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist C))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist P))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist N))) =
          some (RegularCauchyUniformityUp.mk R W D E H C P N)
      rw [RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode N]

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyUniformityUp} :
    regularCauchyUniformityToEventFlow x = regularCauchyUniformityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) =
        regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow y) :=
    congrArg regularCauchyUniformityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip y)))

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_field_faithful :
    forall x y : RegularCauchyUniformityUp,
      regularCauchyUniformityFields x = regularCauchyUniformityFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyUniformityBHistCarrier : BHistCarrier RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyUniformityToEventFlow
  fromEventFlow := regularCauchyUniformityFromEventFlow

instance regularCauchyUniformityChapterTasteGate : ChapterTasteGate RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) = some x
    exact RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyUniformityFieldFaithful : FieldFaithful RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyUniformityFields
  field_faithful := RegularCauchyUniformityTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyUniformityNontrivial : Nontrivial RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyUniformityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyUniformityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyUniformityUp) ∧
      Nonempty (FieldFaithful RegularCauchyUniformityUp) ∧
        Nonempty (Nontrivial RegularCauchyUniformityUp) ∧
          (∀ h : BHist,
            regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyUniformityUp,
              regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyUniformityUp,
                regularCauchyUniformityToEventFlow x = regularCauchyUniformityToEventFlow y ->
                  x = y) ∧
                regularCauchyUniformityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyUniformityChapterTasteGate⟩
  · constructor
    · exact ⟨regularCauchyUniformityFieldFaithful⟩
    · constructor
      · exact ⟨regularCauchyUniformityNontrivial⟩
      · constructor
        · exact RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.RegularCauchyUniformityUp.TasteGate

namespace BEDC.Derived.RegularCauchyUniformityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyUniformityCarrier [AskSetup] [PackageSetup]
    (R W D E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory H ∧
    UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont R W D ∧ Cont W D E ∧
      Cont E H C ∧ PkgSig bundle P pkg

theorem RegularCauchyUniformityCarrier_dyadic_entourage_stability [AskSetup] [PackageSetup]
    {R W D E H C P N W1 W2 E1 E2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyUniformityCarrier R W D E H C P N bundle pkg ->
      Cont W D W1 ->
        Cont W D W2 ->
          Cont W1 E E1 ->
            Cont W2 E E2 ->
              PkgSig bundle E2 pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row E2 ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row E ∨
                      hsame row W1 ∨ hsame row W2 ∨ hsame row E2)
                  (fun row : BHist =>
                    hsame row E2 ∧ PkgSig bundle P pkg ∧ PkgSig bundle E2 pkg)
                  hsame ∧ UnaryHistory W1 ∧ UnaryHistory W2 ∧ UnaryHistory E1 ∧
                    UnaryHistory E2 ∧ hsame E1 E2 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier leftWindowRoute rightWindowRoute leftEntourageRoute rightEntourageRoute
    e2Pkg
  obtain ⟨_rUnary, wUnary, dUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _sourceWindowDyadic, _windowDyadicEntourage, _entourageTransportReplay,
    provenancePkg⟩ := carrier
  have w1Unary : UnaryHistory W1 :=
    unary_cont_closed wUnary dUnary leftWindowRoute
  have w2Unary : UnaryHistory W2 :=
    unary_cont_closed wUnary dUnary rightWindowRoute
  have e1Unary : UnaryHistory E1 :=
    unary_cont_closed w1Unary eUnary leftEntourageRoute
  have e2Unary : UnaryHistory E2 :=
    unary_cont_closed w2Unary eUnary rightEntourageRoute
  have sameWindow : hsame W1 W2 :=
    cont_deterministic leftWindowRoute rightWindowRoute
  have transportedLeftRoute : Cont W2 E E1 :=
    by
      cases sameWindow
      exact leftEntourageRoute
  have sameEntourage : hsame E1 E2 :=
    cont_deterministic transportedLeftRoute rightEntourageRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row E2 ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row E ∨ hsame row W1 ∨
            hsame row W2 ∨ hsame row E2)
        (fun row : BHist =>
          hsame row E2 ∧ PkgSig bundle P pkg ∧ PkgSig bundle E2 pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro E2 ⟨hsame_refl E2, e2Unary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, provenancePkg, e2Pkg⟩
  }
  exact ⟨cert, w1Unary, w2Unary, e1Unary, e2Unary, sameEntourage⟩

end BEDC.Derived.RegularCauchyUniformityUp
