import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubnetSelectorUp

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

inductive RegularCauchySubnetSelectorUp : Type where
  | mk (X I W R D E T H C P N : BHist) : RegularCauchySubnetSelectorUp
  deriving DecidableEq

def RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_encodeBHist h

def RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fields :
    RegularCauchySubnetSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubnetSelectorUp.mk X I W R D E T H C P N =>
      [X, I, W, R, D, E, T, H, C, P, N]

def RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow :
    RegularCauchySubnetSelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fields x).map
      RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_encodeBHist

def RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegularCauchySubnetSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | X :: I :: W :: R :: D :: E :: T :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchySubnetSelectorUp.mk
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist X)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist I)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist W)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist R)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist D)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist E)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist T)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist H)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist C)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist P)
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySubnetSelectorUp,
      RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X I W R D E T H C P N =>
      simp only [RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow,
        RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fields,
        RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow,
        List.map_cons, List.map_nil,
        RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decode_encode]

private theorem RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySubnetSelectorUp} :
    RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow x =
        RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow
            (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow x) :=
        (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow
            (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y :=
        RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RegularCauchySubnetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow

instance RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RegularCauchySubnetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchySubnetSelectorTasteGate_single_carrier_alignment :
    (∀ X I W R D E T H C P N : BHist,
      RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_fields
          (RegularCauchySubnetSelectorUp.mk X I W R D E T H C P N) =
        [X, I, W, R, D, E, T, H, C, P, N]) ∧
      (∀ h : BHist,
        RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decodeBHist
            (RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
        RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_encodeBHist
            (BHist.e1 BHist.Empty) =
          [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨(fun _ _ _ _ _ _ _ _ _ _ _ => rfl),
      RegularCauchySubnetSelectorTasteGate_single_carrier_alignment_decode_encode, rfl⟩

def RegularCauchySubnetSelectorCarrier [AskSetup] [PackageSetup]
    (source index window readback dyadic realSeal tailWitness transportRow replayRow
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory source ∧ UnaryHistory index ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
      UnaryHistory tailWitness ∧ UnaryHistory transportRow ∧ UnaryHistory replayRow ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont index window readback ∧
          Cont readback realSeal tailWitness ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem RegularCauchySubnetSelectorCarrier_handoff [AskSetup] [PackageSetup]
    {source index window readback dyadic realSeal tailWitness transportRow replayRow
      provenance localName selectedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySubnetSelectorCarrier source index window readback dyadic realSeal
        tailWitness transportRow replayRow provenance localName bundle pkg →
      Cont index window selectedRead →
        Cont selectedRead readback sealRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle localName pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row index ∨ hsame row window ∨
                      hsame row readback ∨ hsame row dyadic ∨ hsame row realSeal ∨
                        hsame row tailWitness ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont index window selectedRead ∧
                      Cont selectedRead readback sealRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg)
                  hsame ∧ UnaryHistory selectedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier indexWindow selectedReadback provenancePkg namePkg
  obtain ⟨_sourceUnary, indexUnary, windowUnary, readbackUnary, _dyadicUnary,
    _realSealUnary, _tailWitnessUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _carrierIndexWindow, _carrierReadbackSeal, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed indexUnary windowUnary indexWindow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectedReadUnary readbackUnary selectedReadback
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row index ∨ hsame row window ∨
              hsame row readback ∨ hsame row dyadic ∨ hsame row realSeal ∨
                hsame row tailWitness ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont index window selectedRead ∧
              Cont selectedRead readback sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, indexWindow, selectedReadback, provenancePkg, namePkg⟩
  }
  exact ⟨cert, selectedReadUnary, sealReadUnary⟩

end BEDC.Derived.RegularCauchySubnetSelectorUp
