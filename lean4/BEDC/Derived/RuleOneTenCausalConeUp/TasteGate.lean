import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuleOneTenCausalConeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuleOneTenCausalConeUp : Type where
  | mk (I U T L B O H C P N : BHist) : RuleOneTenCausalConeUp
  deriving DecidableEq

def ruleOneTenCausalConeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ruleOneTenCausalConeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ruleOneTenCausalConeEncodeBHist h

def ruleOneTenCausalConeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ruleOneTenCausalConeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ruleOneTenCausalConeDecodeBHist tail)

private theorem ruleOneTenCausalConeDecodeEncodeBHist :
    ∀ h : BHist, ruleOneTenCausalConeDecodeBHist
      (ruleOneTenCausalConeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ruleOneTenCausalConeFields : RuleOneTenCausalConeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RuleOneTenCausalConeUp.mk I U T L B O H C P N => [I, U, T, L, B, O, H, C, P, N]

def ruleOneTenCausalConeToEventFlow : RuleOneTenCausalConeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ruleOneTenCausalConeFields x).map ruleOneTenCausalConeEncodeBHist

private def ruleOneTenCausalConeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ruleOneTenCausalConeEventAtDefault index rest

def ruleOneTenCausalConeFromEventFlow
    (flow : EventFlow) : Option RuleOneTenCausalConeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RuleOneTenCausalConeUp.mk
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 0 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 1 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 2 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 3 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 4 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 5 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 6 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 7 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 8 flow))
      (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEventAtDefault 9 flow)))

private theorem ruleOneTenCausalCone_round_trip :
    ∀ x : RuleOneTenCausalConeUp,
      ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I U T L B O H C P N =>
      change
        some
          (RuleOneTenCausalConeUp.mk
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist I))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist U))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist T))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist L))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist B))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist O))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist H))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist C))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist P))
            (ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist N))) =
          some (RuleOneTenCausalConeUp.mk I U T L B O H C P N)
      rw [ruleOneTenCausalConeDecodeEncodeBHist I,
        ruleOneTenCausalConeDecodeEncodeBHist U,
        ruleOneTenCausalConeDecodeEncodeBHist T,
        ruleOneTenCausalConeDecodeEncodeBHist L,
        ruleOneTenCausalConeDecodeEncodeBHist B,
        ruleOneTenCausalConeDecodeEncodeBHist O,
        ruleOneTenCausalConeDecodeEncodeBHist H,
        ruleOneTenCausalConeDecodeEncodeBHist C,
        ruleOneTenCausalConeDecodeEncodeBHist P,
        ruleOneTenCausalConeDecodeEncodeBHist N]

private theorem ruleOneTenCausalConeToEventFlow_injective
    {x y : RuleOneTenCausalConeUp} :
    ruleOneTenCausalConeToEventFlow x = ruleOneTenCausalConeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow x) =
        ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow y) :=
    congrArg ruleOneTenCausalConeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ruleOneTenCausalCone_round_trip x).symm
      (Eq.trans hread (ruleOneTenCausalCone_round_trip y)))

private theorem ruleOneTenCausalCone_fields_faithful :
    ∀ x y : RuleOneTenCausalConeUp,
      ruleOneTenCausalConeFields x = ruleOneTenCausalConeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance ruleOneTenCausalConeBHistCarrier : BHistCarrier RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ruleOneTenCausalConeToEventFlow
  fromEventFlow := ruleOneTenCausalConeFromEventFlow

instance ruleOneTenCausalConeChapterTasteGate : ChapterTasteGate RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ruleOneTenCausalConeFromEventFlow (ruleOneTenCausalConeToEventFlow x) = some x
    exact ruleOneTenCausalCone_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ruleOneTenCausalConeToEventFlow_injective heq)

instance ruleOneTenCausalConeFieldFaithful : FieldFaithful RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ruleOneTenCausalConeFields
  field_faithful := ruleOneTenCausalCone_fields_faithful

instance ruleOneTenCausalConeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RuleOneTenCausalConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RuleOneTenCausalConeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RuleOneTenCausalConeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RuleOneTenCausalConeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RuleOneTenCausalConeUp) ∧
      Nonempty (FieldFaithful RuleOneTenCausalConeUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RuleOneTenCausalConeUp) ∧
      (∀ h : BHist,
        ruleOneTenCausalConeDecodeBHist (ruleOneTenCausalConeEncodeBHist h) = h) ∧
      ruleOneTenCausalConeDecodeBHist (BMark.b0 :: []) = BHist.e0 BHist.Empty ∧
      (∀ x y : RuleOneTenCausalConeUp,
        ruleOneTenCausalConeFields x = ruleOneTenCausalConeFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨ruleOneTenCausalConeChapterTasteGate⟩,
      ⟨ruleOneTenCausalConeFieldFaithful⟩,
      ⟨ruleOneTenCausalConeNontrivial⟩,
      ruleOneTenCausalConeDecodeEncodeBHist,
      rfl,
      ruleOneTenCausalCone_fields_faithful⟩

end BEDC.Derived.RuleOneTenCausalConeUp.TasteGate

namespace BEDC.Derived.RuleOneTenCausalConeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RuleOneTenCausalConeCarrier [AskSetup] [PackageSetup]
    (I U T L B O H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory I ∧ UnaryHistory U ∧ UnaryHistory T ∧ UnaryHistory L ∧
    UnaryHistory B ∧ UnaryHistory O ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont I U O ∧ Cont L B C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RuleOneTenCausalConeCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I U T L B O H C P N coneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RuleOneTenCausalConeCarrier I U T L B O H C P N bundle pkg ->
      Cont I U coneRead -> PkgSig bundle coneRead pkg ->
        SemanticNameCert
          (fun row : BHist => hsame row coneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row U ∨ hsame row T ∨ hsame row L ∨
              hsame row B ∨ hsame row O ∨ hsame row coneRead)
          (fun row : BHist =>
            hsame row coneRead ∧ Cont I U coneRead ∧ PkgSig bundle coneRead pkg)
          hsame ∧
          UnaryHistory I ∧ UnaryHistory U ∧ UnaryHistory T ∧ UnaryHistory L ∧
            UnaryHistory B ∧ UnaryHistory O ∧ UnaryHistory coneRead ∧
              Cont I U coneRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier coneRoute conePkg
  obtain ⟨iUnary, uUnary, tUnary, lUnary, bUnary, oUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierConeRoute, _boundaryReplay, pPkg, nPkg⟩ := carrier
  have coneUnary : UnaryHistory coneRead := unary_cont_closed iUnary uUnary coneRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row coneRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row I ∨ hsame row U ∨ hsame row T ∨ hsame row L ∨ hsame row B ∨
            hsame row O ∨ hsame row coneRead)
        (fun row : BHist =>
          hsame row coneRead ∧ Cont I U coneRead ∧ PkgSig bundle coneRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro coneRead ⟨hsame_refl coneRead, coneUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, coneRoute, conePkg⟩
  }
  exact
    ⟨cert, iUnary, uUnary, tUnary, lUnary, bUnary, oUnary, coneUnary, coneRoute,
      pPkg, nPkg⟩

end BEDC.Derived.RuleOneTenCausalConeUp
