import BEDC.Derived.QuotientSoundnessBoundaryUp.RootTransportAudit

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_root_quotsound_nonimport_certificate
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont refusalRead transportRead auditRead ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle auditRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                        hsame row auditRead)
                    (fun row : BHist =>
                      Cont e a v ∧ Cont v t refusalRead ∧
                        Cont t h transportRead ∧ Cont refusalRead transportRead row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧ hsame h n)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport refusalTransportAudit _refusalPkg _transportPkg
    auditPkg
  have sourceAudit :
      (fun row : BHist =>
        QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
          hsame row auditRead) auditRead := by
    exact ⟨carrier, hsame_refl auditRead⟩
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed refusalUnary transportUnary refusalTransportAudit
  exact {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAudit
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨eAV, vTRefusal, tHTransport,
          cont_result_hsame_transport refusalTransportAudit (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport auditUnary (hsame_symm source.right), auditPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
