import BEDC.Derived.BoundedRealSequenceUp.RegularReadbackStability

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealSequenceCarrier_dyadic_bound_transport [AskSetup] [PackageSetup]
    {S W Q R I H C P N S' W' Q' R' I' H' C' P' N' windowRead readbackRead
      sealRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg ->
      NameCertObligations.BoundedRealSequenceCarrier S' W' Q' R' I' H' C' P' N'
          bundle pkg ->
        hsame S S' ->
          hsame W W' ->
            hsame Q Q' ->
              hsame R R' ->
                hsame I I' ->
                  Cont S W windowRead ->
                    Cont windowRead Q readbackRead ->
                      Cont readbackRead R sealRead ->
                        Cont sealRead I boundRead ->
                          PkgSig bundle sealRead pkg ->
                            PkgSig bundle boundRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row S ∨ hsame row W ∨ hsame row Q ∨
                                      hsame row R ∨ hsame row I ∨ hsame row sealRead ∨
                                        hsame row boundRead)
                                  (fun row : BHist =>
                                    hsame row boundRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle P' pkg ∧ PkgSig bundle sealRead pkg ∧
                                        PkgSig bundle boundRead pkg)
                                  hsame ∧
                                UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory boundRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier carrier' _sameS _sameW _sameQ _sameR _sameI sourceWindow
    windowReadback readbackSeal sealBound sealPkg boundPkg
  obtain ⟨SUnary, WUnary, QUnary, RUnary, IUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _intervalRoute, _transportSame, carrierPkg, _localCertPkg⟩ := carrier
  obtain ⟨_SUnary', _WUnary', _QUnary', _RUnary', _IUnary', _HUnary', _CUnary',
    _PUnary', _NUnary', _intervalRoute', _transportSame', carrierPkg',
    _localCertPkg'⟩ := carrier'
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed SUnary WUnary sourceWindow
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary QUnary windowReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary RUnary readbackSeal
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed sealUnary IUnary sealBound
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨
              hsame row I ∨ hsame row sealRead ∨ hsame row boundRead)
          (fun row : BHist =>
            hsame row boundRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle P' pkg ∧
              PkgSig bundle sealRead pkg ∧ PkgSig bundle boundRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundRead ⟨hsame_refl boundRead, boundUnary⟩
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
      exact ⟨source.left, carrierPkg, carrierPkg', sealPkg, boundPkg⟩
  }
  exact ⟨cert, windowUnary, readbackUnary, sealUnary, boundUnary⟩

end BEDC.Derived.BoundedRealSequenceUp
