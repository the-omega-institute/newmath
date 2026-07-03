import BEDC.Derived.RegularCauchyAdditionUp.TasteGate

namespace BEDC.Derived.RegularCauchyAdditionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAdditionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {R0 R1 W0 W1 T0 T1 D S E Z H C P N sourceRead endpointRead ledgerRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyAdditionCarrier R0 R1 W0 W1 T0 T1 D S E Z H C P N bundle pkg ->
      Cont R0 R1 sourceRead ->
        Cont T0 T1 endpointRead ->
          Cont D E ledgerRead ->
            Cont S Z sealRead ->
              PkgSig bundle sealRead pkg ->
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
                    UnaryHistory ledgerRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyAdditionCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute endpointRoute ledgerRoute sealRoute sealPkg
  obtain ⟨r0Unary, r1Unary, _w0Unary, _w1Unary, t0Unary, t1Unary, dUnary, sUnary,
    eUnary, zUnary, _hUnary, _cUnary, _pUnary, _nUnary, _R0R1W0, _W0W1T0, _T0T1D,
    _DEH, _HCS, _SZP, _provenanceSig, _nameSig⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed r0Unary r1Unary sourceRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed t0Unary t1Unary endpointRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed dUnary eUnary ledgerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sUnary zUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R0 ∨ hsame row R1 ∨ hsame row W0 ∨ hsame row W1 ∨
              hsame row T0 ∨ hsame row T1 ∨ hsame row D ∨ hsame row S ∨
                hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                  hsame row P ∨ hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R0 R1 sourceRead ∧ Cont T0 T1 endpointRead ∧
              Cont D E ledgerRead ∧ Cont S Z sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sourceRoute, endpointRoute, ledgerRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, sourceUnary, endpointUnary, ledgerUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyAdditionUp
