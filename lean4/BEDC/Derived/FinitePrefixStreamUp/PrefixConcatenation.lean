import BEDC.Derived.FinitePrefixStreamUp.NameCertObligations

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixStreamCertificatePrefixConcatenation [AskSetup] [PackageSetup]
    {pref certificate extension concatRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory pref ->
      UnaryHistory certificate ->
        UnaryHistory extension ->
          Cont pref extension concatRead ->
            Cont concatRead certificate namedRead ->
              PkgSig bundle certificate pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row pref ∨ hsame row extension ∨ hsame row concatRead ∨
                        hsame row certificate ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont pref extension concatRead ∧
                        Cont concatRead certificate namedRead ∧ PkgSig bundle certificate pkg)
                    hsame ∧
                  UnaryHistory concatRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FinitePrefixStreamCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro prefUnary certificateUnary extensionUnary concatRoute namedRoute packageRead
  have concatUnary : UnaryHistory concatRead :=
    unary_cont_closed prefUnary extensionUnary concatRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed concatUnary certificateUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row pref ∨ hsame row extension ∨ hsame row concatRead ∨
              hsame row certificate ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont pref extension concatRead ∧
              Cont concatRead certificate namedRead ∧ PkgSig bundle certificate pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, concatRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, concatUnary, namedUnary⟩

end BEDC.Derived.FinitePrefixStreamUp
