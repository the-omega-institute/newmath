import BEDC.Derived.RegularCauchyAdditionUp.TasteGate
import BEDC.Derived.RegularCauchyWindowFusionUp.CofinalTailClosure
import BEDC.Derived.RegularCauchyWindowFusionUp.PublicExport

namespace BEDC.Derived.RegularCauchyAdditionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyWindowFusionUp

theorem RegularCauchyAdditionCarrier_window_fusion_boundary [AskSetup] [PackageSetup]
    {R0 R1 W0 W1 T0 T1 D S E Z H C P N sourceRead endpointRead ledgerRead sumSeal
      tailRead budgetRead fusedSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyAdditionCarrier R0 R1 W0 W1 T0 T1 D S E Z H C P N bundle pkg →
      RegularCauchyWindowFusionCarrier R0 W0 S D E H C P N bundle pkg →
        Cont R0 R1 sourceRead →
          Cont T0 T1 endpointRead →
            Cont D E ledgerRead →
              Cont S Z sumSeal →
                Cont W0 S tailRead →
                  Cont S D budgetRead →
                    Cont tailRead budgetRead fusedSeal →
                      Cont H fusedSeal publicRead →
                        PkgSig bundle sumSeal pkg →
                          PkgSig bundle publicRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row R0 ∨ hsame row R1 ∨ hsame row W0 ∨
                                    hsame row W1 ∨ hsame row T0 ∨ hsame row T1 ∨
                                      hsame row D ∨ hsame row S ∨ hsame row E ∨
                                        hsame row Z ∨ hsame row H ∨ hsame row C ∨
                                          hsame row P ∨ hsame row N ∨ hsame row sumSeal ∨
                                            hsame row publicRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S Z sumSeal ∧
                                    Cont H fusedSeal publicRead ∧
                                      PkgSig bundle publicRead pkg)
                                hsame ∧
                              UnaryHistory sumSeal ∧ UnaryHistory publicRead ∧
                                PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro additionCarrier fusionCarrier sourceRoute endpointRoute ledgerRoute sumRoute
    tailRoute budgetRoute fusedRoute publicRoute sumPkg publicPkg
  have additionHandoff :=
    RegularCauchyAdditionCarrier_real_seal_handoff
      (R0 := R0) (R1 := R1) (W0 := W0) (W1 := W1) (T0 := T0) (T1 := T1)
      (D := D) (S := S) (E := E) (Z := Z) (H := H) (C := C) (P := P)
      (N := N) (sourceRead := sourceRead) (endpointRead := endpointRead)
      (ledgerRead := ledgerRead) (sealRead := sumSeal) (bundle := bundle) (pkg := pkg)
      additionCarrier sourceRoute endpointRoute ledgerRoute sumRoute sumPkg
  obtain ⟨_r0AddUnary, _r1AddUnary, _t0Unary, _t1Unary, _dAddUnary, _eAddUnary,
    _sAddUnary, _zUnary, sumUnary, _sourceRoute, _endpointRoute, _ledgerRoute,
    _sumRoute, _additionPkg, _sumPkg⟩ := additionHandoff
  obtain ⟨r0Unary, w0Unary, sUnary, dUnary, eUnary, hUnary, _cUnary, _pUnary,
    _nUnary, provenancePkg, _namePkg⟩ := fusionCarrier
  have publicExport :=
    RegularCauchyWindowFusionPublicExport
      (R := R0) (W := W0) (S := S) (D := D) (E := E) (H := H) (C := C)
      (P := P) (N := N) (tailRead := tailRead) (budgetRead := budgetRead)
      (sealRead := fusedSeal) (publicRead := publicRead) (bundle := bundle) (pkg := pkg)
      r0Unary w0Unary sUnary dUnary eUnary hUnary tailRoute budgetRoute fusedRoute
      publicRoute provenancePkg publicPkg
  obtain ⟨_publicCert, _tailUnary, _budgetUnary, _fusedUnary, publicUnary⟩ :=
    publicExport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R0 ∨ hsame row R1 ∨ hsame row W0 ∨ hsame row W1 ∨
              hsame row T0 ∨ hsame row T1 ∨ hsame row D ∨ hsame row S ∨
                hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                  hsame row P ∨ hsame row N ∨ hsame row sumSeal ∨
                    hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S Z sumSeal ∧ Cont H fusedSeal publicRead ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sumRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, sumUnary, publicUnary, provenancePkg⟩

end BEDC.Derived.RegularCauchyAdditionUp
