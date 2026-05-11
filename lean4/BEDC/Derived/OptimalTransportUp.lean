import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptimalTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OptimalTransportFiniteCouplingCarrier [AskSetup] [PackageSetup]
    (source target sourceMass targetMass cost coupling sourceMarginal targetMarginal objective
      feasible dual provenance : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory sourceMass ∧
    UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      Cont source coupling sourceMarginal ∧ Cont target coupling targetMarginal ∧
        Cont cost coupling objective ∧ Cont objective feasible dual ∧
          Cont dual sourceMarginal provenance ∧ PkgSig bundle provenance pkg

theorem OptimalTransportFiniteCouplingCarrier_marginal_ledger [AskSetup] [PackageSetup]
    {source target sourceMass targetMass cost coupling sourceMarginal targetMarginal objective
      feasible dual provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingCarrier source target sourceMass targetMass cost coupling
        sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧
        hsame sourceMarginal (append source coupling) ∧
          hsame targetMarginal (append target coupling) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨sourceUnary, targetUnary, _sourceMassUnary, _targetMassUnary, _costUnary,
    couplingUnary, sourceMarginalRow, targetMarginalRow, _objectiveRow, _dualRow,
    _provenanceRow, pkgRow⟩ := carrier
  have sourceMarginalUnary : UnaryHistory sourceMarginal :=
    unary_cont_closed sourceUnary couplingUnary sourceMarginalRow
  have targetMarginalUnary : UnaryHistory targetMarginal :=
    unary_cont_closed targetUnary couplingUnary targetMarginalRow
  exact
    ⟨sourceMarginalUnary, targetMarginalUnary, sourceMarginalRow, targetMarginalRow, pkgRow⟩

theorem OptimalTransportFiniteCouplingCarrier_cost_summation_ledger
    [AskSetup] [PackageSetup]
    {source target sourceMass targetMass cost coupling sourceMarginal targetMarginal objective
      feasible dual provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingCarrier source target sourceMass targetMass cost coupling
        sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      UnaryHistory cost ∧ UnaryHistory coupling ∧ UnaryHistory objective ∧
        hsame objective (append cost coupling) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_sourceUnary, _targetUnary, _sourceMassUnary, _targetMassUnary, costUnary,
    couplingUnary, _sourceMarginalRow, _targetMarginalRow, objectiveRow, _dualRow,
    _provenanceRow, pkgRow⟩ := carrier
  have objectiveUnary : UnaryHistory objective :=
    unary_cont_closed costUnary couplingUnary objectiveRow
  exact ⟨costUnary, couplingUnary, objectiveUnary, objectiveRow, pkgRow⟩

theorem OptimalTransportFiniteCouplingCarrier_lpduality_feasible_surface
    [AskSetup] [PackageSetup]
    {source target sourceMass targetMass cost coupling sourceMarginal targetMarginal objective
      feasible dual provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingCarrier source target sourceMass targetMass cost coupling
        sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      UnaryHistory objective ∧ hsame objective (append cost coupling) ∧
        hsame sourceMarginal (append source coupling) ∧
          hsame targetMarginal (append target coupling) ∧ hsame dual (append objective feasible) ∧
            Cont objective feasible dual ∧ Cont dual sourceMarginal provenance ∧
              PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_sourceUnary, _targetUnary, _sourceMassUnary, _targetMassUnary, costUnary,
    couplingUnary, sourceMarginalRow, targetMarginalRow, objectiveRow, dualRow,
    provenanceRow, pkgRow⟩ := carrier
  have objectiveUnary : UnaryHistory objective :=
    unary_cont_closed costUnary couplingUnary objectiveRow
  exact
    ⟨objectiveUnary, objectiveRow, sourceMarginalRow, targetMarginalRow, dualRow,
      dualRow, provenanceRow, pkgRow⟩

def OptimalTransportPacket [AskSetup] [PackageSetup]
    (source target massSource massTarget cost coupling marginal objective feasible dual provenance :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory massSource ∧
    UnaryHistory massTarget ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      UnaryHistory marginal ∧ UnaryHistory objective ∧ UnaryHistory feasible ∧
        UnaryHistory dual ∧ UnaryHistory provenance ∧ Cont source target coupling ∧
          Cont cost coupling objective ∧ Cont marginal objective feasible ∧
            Cont feasible dual provenance ∧ PkgSig bundle provenance pkg

theorem OptimalTransportPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {source target massSource massTarget cost coupling marginal objective feasible dual provenance :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportPacket source target massSource massTarget cost coupling marginal
        objective feasible dual provenance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          OptimalTransportPacket source target massSource massTarget cost coupling marginal
            objective feasible dual provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          OptimalTransportPacket source target massSource massTarget cost coupling marginal
            objective feasible dual provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          OptimalTransportPacket source target massSource massTarget cost coupling marginal
            objective feasible dual provenance bundle pkg ∧ hsame row provenance)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro packet (hsame_refl provenance))
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
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

def OptimalTransportFiniteCouplingPacket [AskSetup] [PackageSetup]
    (sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective feasible dual provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceSupport ∧ UnaryHistory targetSupport ∧ UnaryHistory sourceMass ∧
    UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧ UnaryHistory objective ∧
        UnaryHistory feasible ∧ UnaryHistory dual ∧ UnaryHistory provenance ∧
          Cont coupling sourceMass sourceMarginal ∧
            Cont coupling targetMass targetMarginal ∧ Cont cost coupling objective ∧
              Cont sourceMarginal targetMarginal feasible ∧ Cont objective feasible dual ∧
                Cont dual provenance provenance ∧ PkgSig bundle provenance pkg

theorem OptimalTransportFiniteCouplingPacket_marginal_ledger [AskSetup] [PackageSetup]
    {sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective feasible dual provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass cost
        coupling sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧
        hsame sourceMarginal (append coupling sourceMass) ∧
          hsame targetMarginal (append coupling targetMass) ∧ PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨_sourceSupportUnary, _targetSupportUnary, _sourceMassUnary, _targetMassUnary,
    _costUnary, _couplingUnary, sourceMarginalUnary, targetMarginalUnary, _objectiveUnary,
    _feasibleUnary, _dualUnary, _provenanceUnary, sourceMarginalRow, targetMarginalRow,
    _objectiveRow, _feasibleRow, _dualRow, _provenanceRow, pkgRow⟩ := packet
  exact ⟨sourceMarginalUnary, targetMarginalUnary, sourceMarginalRow, targetMarginalRow, pkgRow⟩

theorem OptimalTransportFiniteCouplingPacket_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective feasible dual provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass cost
        coupling sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro packet (hsame_refl provenance))
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
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem OptimalTransportFiniteCouplingPacket_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective feasible dual provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass cost
        coupling sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          hsame ∧
        Cont coupling sourceMass sourceMarginal ∧
          Cont coupling targetMass targetMarginal ∧ Cont cost coupling objective ∧
            Cont sourceMarginal targetMarginal feasible ∧ Cont objective feasible dual ∧
              Cont dual provenance provenance ∧ PkgSig bundle provenance pkg := by
  intro packet
  have packetProof := packet
  obtain ⟨_sourceSupportUnary, _targetSupportUnary, _sourceMassUnary, _targetMassUnary,
    _costUnary, _couplingUnary, _sourceMarginalUnary, _targetMarginalUnary, _objectiveUnary,
    _feasibleUnary, _dualUnary, _provenanceUnary, sourceMarginalRow, targetMarginalRow,
    objectiveRow, feasibleRow, dualRow, provenanceRow, pkgRow⟩ := packet
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro packetProof (hsame_refl provenance))
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
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact
    ⟨cert, sourceMarginalRow, targetMarginalRow, objectiveRow, feasibleRow, dualRow,
      provenanceRow, pkgRow⟩

theorem OptimalTransportFiniteCouplingPacket_public_export_surface
    [AskSetup] [PackageSetup]
    {sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective feasible dual provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass cost
        coupling sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass
              cost coupling sourceMarginal targetMarginal objective feasible dual provenance
              bundle pkg ∧ hsame row provenance)
          hsame ∧
        UnaryHistory sourceSupport ∧ UnaryHistory targetSupport ∧ UnaryHistory sourceMass ∧
          UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
            UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧
              UnaryHistory objective ∧ UnaryHistory feasible ∧ UnaryHistory dual ∧
                UnaryHistory provenance ∧ Cont coupling sourceMass sourceMarginal ∧
                  Cont coupling targetMass targetMarginal ∧ Cont cost coupling objective ∧
                    Cont sourceMarginal targetMarginal feasible ∧ Cont objective feasible dual ∧
                      Cont dual provenance provenance ∧ PkgSig bundle provenance pkg := by
  intro packet
  have cert :=
    OptimalTransportFiniteCouplingPacket_semantic_name_certificate
      (sourceSupport := sourceSupport) (targetSupport := targetSupport)
      (sourceMass := sourceMass) (targetMass := targetMass) (cost := cost)
      (coupling := coupling) (sourceMarginal := sourceMarginal)
      (targetMarginal := targetMarginal) (objective := objective) (feasible := feasible)
      (dual := dual) (provenance := provenance) (bundle := bundle) (pkg := pkg) packet
  obtain ⟨sourceSupportUnary, targetSupportUnary, sourceMassUnary, targetMassUnary, costUnary,
    couplingUnary, sourceMarginalUnary, targetMarginalUnary, objectiveUnary, feasibleUnary,
    dualUnary, provenanceUnary, sourceMarginalRow, targetMarginalRow, objectiveRow,
    feasibleRow, dualRow, provenanceRow, pkgRow⟩ := packet
  exact
    ⟨cert, sourceSupportUnary, targetSupportUnary, sourceMassUnary, targetMassUnary, costUnary,
      couplingUnary, sourceMarginalUnary, targetMarginalUnary, objectiveUnary, feasibleUnary,
      dualUnary, provenanceUnary, sourceMarginalRow, targetMarginalRow, objectiveRow,
      feasibleRow, dualRow, provenanceRow, pkgRow⟩

end BEDC.Derived.OptimalTransportUp
