import BEDC.Derived.RegularCauchyAdditionUp.NameCertObligations
import BEDC.Derived.RegularCauchyAdditionUp.WindowSumStability

namespace BEDC.Derived.RegularCauchyAdditionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAdditionCarrier_sibling_dependency_route [AskSetup] [PackageSetup]
    {R0 R1 W0 W1 T0 T1 D S E Z H C P N sourceRead endpointRead ledgerRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyAdditionCarrier R0 R1 W0 W1 T0 T1 D S E Z H C P N bundle pkg →
      Cont R0 R1 sourceRead →
        Cont T0 T1 endpointRead →
          Cont D E ledgerRead →
            Cont S Z sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row R0 ∨ hsame row R1 ∨ hsame row W0 ∨ hsame row W1 ∨
                        hsame row T0 ∨ hsame row T1 ∨ hsame row D ∨ hsame row S ∨
                          hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont R0 R1 sourceRead ∧
                        Cont T0 T1 endpointRead ∧ Cont D E ledgerRead ∧
                          Cont S Z sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory endpointRead ∧
                    UnaryHistory ledgerRead ∧ UnaryHistory sealRead ∧
                      Cont R0 R1 sourceRead ∧ Cont T0 T1 endpointRead ∧
                        Cont D E ledgerRead ∧ Cont S Z sealRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute endpointRoute ledgerRoute sealRoute sealPkg
  have obligations :=
    RegularCauchyAdditionCarrier_namecert_obligations
      (R0 := R0) (R1 := R1) (W0 := W0) (W1 := W1) (T0 := T0) (T1 := T1)
      (D := D) (S := S) (E := E) (Z := Z) (H := H) (C := C) (P := P)
      (N := N) (sourceRead := sourceRead) (endpointRead := endpointRead)
      (ledgerRead := ledgerRead) (sealRead := sealRead) (bundle := bundle) (pkg := pkg)
      carrier sourceRoute endpointRoute ledgerRoute sealRoute sealPkg
  obtain ⟨cert, sourceUnary, endpointUnary, ledgerUnary, sealUnary⟩ := obligations
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, _t0Unary, _t1Unary, _dUnary,
    _sUnary, _eUnary, _zUnary, _hUnary, _cUnary, _pUnary, _nUnary, _sourceCarrier,
    _windowCarrier, _endpointCarrier, _ledgerCarrier, _sealCarrier, _provenanceCarrier,
    pPkg, _nPkg⟩ := carrier
  exact
    ⟨cert, sourceUnary, endpointUnary, ledgerUnary, sealUnary, sourceRoute, endpointRoute,
      ledgerRoute, sealRoute, pPkg, sealPkg⟩

end BEDC.Derived.RegularCauchyAdditionUp
