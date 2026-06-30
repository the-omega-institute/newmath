import BEDC.Derived.ReflectiveInquiryUp.Carrier

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectiveInquiryGroundCompilerObligationRoute [AskSetup] [PackageSetup]
    {P F S K A R L H C Q N compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectiveInquiryCarrier P F S K A R L H C Q N bundle pkg ->
      Cont C Q compilerRead ->
        PkgSig bundle compilerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row compilerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row P ∨ hsame row F ∨ hsame row S ∨ hsame row K ∨
                  hsame row A ∨ hsame row R ∨ hsame row L ∨ hsame row H ∨
                    hsame row C ∨ hsame row Q ∨ hsame row N ∨ hsame row compilerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C Q compilerRead ∧
                  PkgSig bundle compilerRead pkg)
              hsame ∧
            UnaryHistory compilerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier compilerRoute compilerPkg
  obtain ⟨_pUnary, _fUnary, _sUnary, _kUnary, _aUnary, _rUnary, _lUnary, _hUnary,
    cUnary, qUnary, _nUnary, _pfRoute, _skRoute, _rlRoute, _hcRoute, _nPkg⟩ := carrier
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed cUnary qUnary compilerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compilerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row F ∨ hsame row S ∨ hsame row K ∨
              hsame row A ∨ hsame row R ∨ hsame row L ∨ hsame row H ∨
                hsame row C ∨ hsame row Q ∨ hsame row N ∨ hsame row compilerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C Q compilerRead ∧ PkgSig bundle compilerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compilerRead ⟨hsame_refl compilerRead, compilerUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compilerRoute, compilerPkg⟩
  }
  exact ⟨cert, compilerUnary⟩

end BEDC.Derived.ReflectiveInquiryUp
