import BEDC.Derived.CauchyProductUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductUp : Type where
  | mk
      (sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
        classifier transport routes ledger name : BHist) :
      CauchyProductUp
  deriving DecidableEq

def CauchyProductTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyProductTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyProductTasteGate_single_carrier_alignment_encodeBHist h

def CauchyProductTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CauchyProductTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CauchyProductTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyProductTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyProductTasteGate_single_carrier_alignment_decodeBHist
          (CauchyProductTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyProductTasteGate_single_carrier_alignment_fields : CauchyProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductUp.mk sourceA sourceB windowA windowB radiusA radiusB observationA
      observationB product classifier transport routes ledger name =>
      [sourceA, sourceB, windowA, windowB, radiusA, radiusB, observationA, observationB,
        product, classifier, transport, routes, ledger, name]

def CauchyProductTasteGate_single_carrier_alignment_toEventFlow :
    CauchyProductUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyProductTasteGate_single_carrier_alignment_fields x).map
      CauchyProductTasteGate_single_carrier_alignment_encodeBHist

def CauchyProductTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | sourceA :: sourceB :: windowA :: windowB :: radiusA :: radiusB :: observationA ::
      observationB :: product :: classifier :: transport :: routes :: ledger :: name :: [] =>
      some
        (CauchyProductUp.mk
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist sourceA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist sourceB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist windowA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist windowB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist radiusA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist radiusB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist observationA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist observationB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist product)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist classifier)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist transport)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist routes)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist ledger)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist name))
  | _ => none

private theorem CauchyProductTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyProductUp,
      CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name =>
      simp only [CauchyProductTasteGate_single_carrier_alignment_toEventFlow,
        CauchyProductTasteGate_single_carrier_alignment_fields,
        CauchyProductTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, CauchyProductTasteGate_single_carrier_alignment_decode_encode]

private theorem CauchyProductTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyProductUp} :
    CauchyProductTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyProductTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyProductTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CauchyProductTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyProductTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CauchyProductTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := CauchyProductTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem CauchyProductTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyProductUp,
      CauchyProductTasteGate_single_carrier_alignment_fields x =
          CauchyProductTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceA₁ sourceB₁ windowA₁ windowB₁ radiusA₁ radiusB₁ observationA₁ observationB₁
      product₁ classifier₁ transport₁ routes₁ ledger₁ name₁ =>
      cases y with
      | mk sourceA₂ sourceB₂ windowA₂ windowB₂ radiusA₂ radiusB₂ observationA₂ observationB₂
          product₂ classifier₂ transport₂ routes₂ ledger₂ name₂ =>
          cases hfields
          rfl

instance CauchyProductTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyProductTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyProductTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyProductTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyProductTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyProductTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CauchyProductTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyProductTasteGate_single_carrier_alignment_fields
  field_faithful := CauchyProductTasteGate_single_carrier_alignment_field_faithful

instance CauchyProductTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyProductUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyProductTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyProductTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CauchyProductTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CauchyProductTasteGate_single_carrier_alignment_decodeBHist
          (CauchyProductTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CauchyProductTasteGate_single_carrier_alignment_fields
          (CauchyProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨CauchyProductTasteGate_single_carrier_alignment_decode_encode, rfl⟩

theorem CauchyProductPacket_observation_budget_triangle [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetEntry budgetWindow budgetDyadic
      budgetReadback budgetSeal budgetTransport budgetClassifier budgetPkgRow budgetName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont observationA observationB product ->
      Cont product budgetEntry budgetSeal ->
        PkgSig bundle budgetSeal pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row product ∨ hsame row budgetSeal ∨ hsame row budgetName)
              (fun row : BHist =>
                hsame row product ∨ hsame row budgetSeal ∨ hsame row budgetName)
              (fun row : BHist =>
                PkgSig bundle budgetSeal pkg ∧
                  (hsame row product ∨ hsame row budgetSeal ∨ hsame row budgetName))
              hsame ∧
            CauchyProductTasteGate_single_carrier_alignment_fields
                (CauchyProductUp.mk sourceA sourceB windowA windowB radiusA radiusB
                  observationA observationB product classifier transport routes ledger name) =
              [sourceA, sourceB, windowA, windowB, radiusA, radiusB, observationA,
                observationB, product, classifier, transport, routes, ledger, name] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _productRoute _budgetRoute budgetPkg
  have sourceProduct :
      (fun row : BHist => hsame row product ∨ hsame row budgetSeal ∨ hsame row budgetName)
        product := by
    exact Or.inl (hsame_refl product)
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row product ∨ hsame row budgetSeal ∨ hsame row budgetName)
        (fun row : BHist => hsame row product ∨ hsame row budgetSeal ∨ hsame row budgetName)
        (fun row : BHist =>
          PkgSig bundle budgetSeal pkg ∧
            (hsame row product ∨ hsame row budgetSeal ∨ hsame row budgetName))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro product sourceProduct
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
        intro _row _other sameRows source
        cases source with
        | inl rowProduct =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowProduct)
        | inr tail =>
            cases tail with
            | inl rowBudgetSeal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowBudgetSeal))
            | inr rowBudgetName =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowBudgetName))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro budgetPkg source
  }
  exact ⟨cert, rfl⟩

theorem CauchyProductPacket_finite_product_budget_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                UnaryHistory budgetSeal ∧ UnaryHistory realSeal ∧
                  Cont product ledger classifier ∧ Cont classifier routes budgetClassifier ∧
                    Cont budgetClassifier ledger budgetSeal ∧ Cont budgetSeal routes realSeal ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary routesUnary realSealRoute
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary, realSealUnary,
      classifierRoute, classifierBudget, budgetSealRoute, realSealRoute, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
