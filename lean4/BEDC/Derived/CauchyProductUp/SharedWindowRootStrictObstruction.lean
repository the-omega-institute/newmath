import BEDC.Derived.CauchyProductUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_window_root_strict_obstruction [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name bypassRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      hsame bypassRead sourceA ->
        Cont bypassRead routes product ->
          PkgSig bundle bypassRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row sourceA ∨ hsame row windowA ∨ hsame row windowB ∨
                    hsame row product ∨ hsame row classifier ∨ hsame row name)
                (fun row : BHist =>
                  hsame row sourceA ∨ hsame row windowA ∨ hsame row windowB ∨
                    hsame row product ∨ hsame row classifier ∨ hsame row name)
                (fun row : BHist =>
                  PkgSig bundle bypassRead pkg ∧
                    (hsame row sourceA ∨ hsame row windowA ∨ hsame row windowB ∨
                      hsame row product ∨ hsame row classifier ∨ hsame row name))
                hsame ∧
              UnaryHistory bypassRead ∧ UnaryHistory product ∧
                Cont bypassRead routes product ∧ PkgSig bundle bypassRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet sameBypassSource bypassProduct bypassPkg
  obtain ⟨sourceAUnary, _sourceBUnary, windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, routesUnary, _ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, _namePkg⟩ := packet
  have bypassUnary : UnaryHistory bypassRead :=
    unary_transport sourceAUnary (hsame_symm sameBypassSource)
  have productUnary : UnaryHistory product :=
    unary_cont_closed bypassUnary routesUnary bypassProduct
  have sourceAtSourceA :
      hsame sourceA sourceA ∨ hsame sourceA windowA ∨ hsame sourceA windowB ∨
        hsame sourceA product ∨ hsame sourceA classifier ∨ hsame sourceA name :=
    Or.inl (hsame_refl sourceA)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row windowA ∨ hsame row windowB ∨
              hsame row product ∨ hsame row classifier ∨ hsame row name)
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row windowA ∨ hsame row windowB ∨
              hsame row product ∨ hsame row classifier ∨ hsame row name)
          (fun row : BHist =>
            PkgSig bundle bypassRead pkg ∧
              (hsame row sourceA ∨ hsame row windowA ∨ hsame row windowB ∨
                hsame row product ∨ hsame row classifier ∨ hsame row name))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceA sourceAtSourceA
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
        cases source with
        | inl rowSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowSource)
        | inr tail =>
            cases tail with
            | inl rowWindowA =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowWindowA))
            | inr tail =>
                cases tail with
                | inl rowWindowB =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowWindowB)))
                | inr tail =>
                    cases tail with
                    | inl rowProduct =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) rowProduct))))
                    | inr tail =>
                        cases tail with
                        | inl rowClassifier =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) rowClassifier)))))
                        | inr rowName =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (hsame_trans (hsame_symm sameRows) rowName)))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro bypassPkg source
  }
  exact ⟨cert, bypassUnary, productUnary, bypassProduct, bypassPkg⟩

end BEDC.Derived.CauchyProductUp
