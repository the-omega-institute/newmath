import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberOpenPhaseSourceNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead endpointRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window phaseRead ->
        Cont phaseRead radius endpointRead ->
          Cont endpointRead route realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row radius ∨ hsame row route ∨
                        hsame row realRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg ∧
                        hsame row realRead)
                    hsame ∧
                UnaryHistory phaseRead ∧ UnaryHistory endpointRead ∧ UnaryHistory realRead ∧
                  Cont cover window phaseRead ∧ Cont phaseRead radius endpointRead ∧
                    Cont endpointRead route realRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coverWindowPhase phaseRadiusEndpoint endpointRouteReal realPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed coverUnary windowUnary coverWindowPhase
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed phaseUnary radiusUnary phaseRadiusEndpoint
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary routeUnary endpointRouteReal
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row radius ∨ hsame row route ∨ hsame row realRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg ∧ hsame row realRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, realPkg, source.left⟩
  }
  exact
    ⟨cert, phaseUnary, endpointUnary, realUnary, coverWindowPhase, phaseRadiusEndpoint,
      endpointRouteReal, provenancePkg, realPkg⟩

theorem FiniteLebesgueNumberRootUnblockExitTriad [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead endpointRead
      realRead triadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window phaseRead ->
        Cont phaseRead radius endpointRead ->
          Cont endpointRead route realRead ->
            Cont realRead nameRow triadRead ->
              PkgSig bundle triadRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row triadRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row phaseRead ∨ hsame row endpointRead ∨ hsame row realRead ∨
                        hsame row triadRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle triadRead pkg ∧
                        hsame row triadRead)
                    hsame ∧
                  UnaryHistory phaseRead ∧ UnaryHistory endpointRead ∧
                    UnaryHistory realRead ∧ UnaryHistory triadRead ∧
                      Cont cover window phaseRead ∧ Cont phaseRead radius endpointRead ∧
                        Cont endpointRead route realRead ∧ Cont realRead nameRow triadRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle triadRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coverWindowPhase phaseRadiusEndpoint endpointRouteReal realNameTriad triadPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed coverUnary windowUnary coverWindowPhase
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed phaseUnary radiusUnary phaseRadiusEndpoint
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary routeUnary endpointRouteReal
  have triadUnary : UnaryHistory triadRead :=
    unary_cont_closed realUnary nameRowUnary realNameTriad
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row triadRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row phaseRead ∨ hsame row endpointRead ∨ hsame row realRead ∨
              hsame row triadRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle triadRead pkg ∧
              hsame row triadRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro triadRead ⟨hsame_refl triadRead, triadUnary⟩
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
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, triadPkg, source.left⟩
  }
  exact
    ⟨cert, phaseUnary, endpointUnary, realUnary, triadUnary, coverWindowPhase,
      phaseRadiusEndpoint, endpointRouteReal, realNameTriad, provenancePkg, triadPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
