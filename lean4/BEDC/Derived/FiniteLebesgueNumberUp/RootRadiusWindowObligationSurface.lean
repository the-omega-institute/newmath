import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberRootRadiusWindowObligationLedger [AskSetup] [PackageSetup]
    (cover window radius mesh stream regular real transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance nameRow
      bundle pkg ∧
    Cont cover radius stream ∧ Cont stream mesh regular ∧ Cont regular replay real ∧
      PkgSig bundle real pkg

theorem FiniteLebesgueNumberRootRadiusWindowObligationLedger_certificate
    [AskSetup] [PackageSetup]
    {cover window radius mesh stream regular real transport replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRootRadiusWindowObligationLedger cover window radius mesh stream regular
        real transport replay provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberRootRadiusWindowObligationLedger cover window radius mesh
                stream regular real transport replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row real ∧ Cont cover radius stream ∧ Cont stream mesh regular ∧
              Cont regular replay real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame ∧
        UnaryHistory cover ∧ UnaryHistory stream ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
          Cont cover radius stream ∧ Cont stream mesh regular ∧ Cont regular replay real ∧
            PkgSig bundle real pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberRootRadiusWindowObligationLedger cover window radius mesh stream
        regular real transport replay provenance nameRow bundle pkg :=
    ledger
  obtain ⟨carrier, coverRadiusStream, streamMeshRegular, regularReplayReal, realPkg⟩ :=
    ledger
  obtain ⟨coverUnary, streamUnary, radiusUnary, meshUnary, _transportUnary, replayUnary,
    _provenanceUnary, _nameRowUnary, _coverStreamRadius, _radiusMeshReplay,
    _replayNameProvenance, _provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory regular :=
    unary_cont_closed streamUnary meshUnary streamMeshRegular
  have realUnary : UnaryHistory real :=
    unary_cont_closed regularUnary replayUnary regularReplayReal
  have sourceReal :
      (fun row : BHist =>
        hsame row real ∧
          FiniteLebesgueNumberRootRadiusWindowObligationLedger cover window radius mesh stream
            regular real transport replay provenance nameRow bundle pkg) real := by
    exact ⟨hsame_refl real, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberRootRadiusWindowObligationLedger cover window radius mesh
                stream regular real transport replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row real ∧ Cont cover radius stream ∧ Cont stream mesh regular ∧
              Cont regular replay real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro real sourceReal
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
            ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, coverRadiusStream, streamMeshRegular, regularReplayReal⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, realPkg⟩
    }
  exact
    ⟨cert, coverUnary, streamUnary, radiusUnary, meshUnary, coverRadiusStream,
      streamMeshRegular, regularReplayReal, realPkg⟩

theorem FiniteLebesgueNumberRootRadiusWindowObligationSurface [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow rootSurface →
        PkgSig bundle rootSurface pkg →
          SemanticNameCert
              (fun row : BHist => hsame row rootSurface ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                  hsame row mesh ∨ hsame row route ∨ hsame row rootSurface)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle rootSurface pkg ∧
                  hsame row rootSurface)
              hsame ∧
            UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
              UnaryHistory mesh ∧ UnaryHistory route ∧ UnaryHistory rootSurface ∧
                Cont cover window radius ∧ Cont radius mesh route ∧
                  Cont route nameRow rootSurface ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle rootSurface pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeNameRoot rootSurfacePkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootSurfaceUnary : UnaryHistory rootSurface :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have rootSurfaceCarrier :
      (fun row : BHist => hsame row rootSurface ∧ UnaryHistory row) rootSurface := by
    exact ⟨hsame_refl rootSurface, rootSurfaceUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootSurface ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row cover ∨ hsame row window ∨ hsame row radius ∨
            hsame row mesh ∨ hsame row route ∨ hsame row rootSurface)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle rootSurface pkg ∧
            hsame row rootSurface)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootSurface rootSurfaceCarrier
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, rootSurfacePkg, source.left⟩
    }
  exact
    ⟨cert, coverUnary, windowUnary, radiusUnary, meshUnary, routeUnary, rootSurfaceUnary,
      coverWindowRadius, radiusMeshRoute, routeNameRoot, provenancePkg, rootSurfacePkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
