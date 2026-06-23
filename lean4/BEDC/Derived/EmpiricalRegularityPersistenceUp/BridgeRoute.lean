import BEDC.Derived.EmpiricalRegularityPersistenceUp.TasteGate

namespace BEDC.Derived.EmpiricalRegularityPersistenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EmpiricalRegularityPersistenceBridgeRoute [AskSetup] [PackageSetup]
    {M R K L G A S F H C P N lawRead publicRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EmpiricalRegularityPersistenceCarrier M R K L G A S F H C P N bundle pkg ->
      Cont A S lawRead ->
        Cont lawRead N publicRead ->
          Cont publicRead P bridgeRead ->
            PkgSig bundle lawRead pkg ->
              PkgSig bundle publicRead pkg ->
                PkgSig bundle bridgeRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                      (fun row : BHist => hsame row bridgeRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
                      hsame ∧
                    UnaryHistory bridgeRead ∧ Cont publicRead P bridgeRead ∧
                      PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier lawRoute publicRoute bridgeRoute lawPkg publicPkg bridgePkg
  have publicSurface :=
    EmpiricalRegularityPersistenceCarrier_public_interface
      (M := M) (R := R) (K := K) (L := L) (G := G) (A := A) (S := S)
      (F := F) (H := H) (C := C) (P := P) (N := N) (lawRead := lawRead)
      (publicRead := publicRead) (bundle := bundle) (pkg := pkg)
      carrier lawRoute publicRoute lawPkg publicPkg
  obtain ⟨_publicCert, publicUnary, _publicCont, _publicPkg⟩ := publicSurface
  have carrierExposure :=
    EmpiricalRegularityPersistenceCarrier_gap_exposure
      (M := M) (R := R) (K := K) (L := L) (G := G) (A := A) (S := S)
      (F := F) (H := H) (C := C) (P := P) (N := N)
      (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨_mUnary, _rUnary, _kUnary, _lUnary, _gUnary, _sUnary, _fUnary,
    _cUnary, pUnary, _nUnary, _mrk, _klg, _gas, _sfh, _pPkg, _nPkg⟩ :=
    carrierExposure
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary pUnary bridgeRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row bridgeRead)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead
        ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary, bridgeRoute, bridgePkg⟩

end BEDC.Derived.EmpiricalRegularityPersistenceUp
