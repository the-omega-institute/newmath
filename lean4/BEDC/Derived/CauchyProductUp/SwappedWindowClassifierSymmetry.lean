import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_swapped_window_classifier_symmetry_certificate
    [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name swappedTransport swappedProduct realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont windowB windowA swappedTransport ->
        Cont observationB observationA swappedProduct ->
          hsame swappedProduct product ->
            Cont classifier routes realSeal ->
              PkgSig bundle realSeal pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row windowA ∨ hsame row windowB ∨ hsame row swappedProduct ∨
                        hsame row classifier ∨ hsame row realSeal)
                    (fun row : BHist =>
                      hsame row windowA ∨ hsame row windowB ∨ hsame row swappedProduct ∨
                        hsame row classifier ∨ hsame row realSeal)
                    (fun row : BHist =>
                      PkgSig bundle realSeal pkg ∧
                        (hsame row windowA ∨ hsame row windowB ∨ hsame row swappedProduct ∨
                          hsame row classifier ∨ hsame row realSeal))
                    hsame ∧
                  UnaryHistory windowA ∧ UnaryHistory windowB ∧
                    UnaryHistory swappedTransport ∧ UnaryHistory swappedProduct ∧
                      UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                        hsame swappedProduct product ∧
                          Cont windowB windowA swappedTransport ∧
                            Cont observationB observationA swappedProduct ∧
                              Cont product ledger classifier ∧
                                Cont classifier routes realSeal ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet swappedWindow swappedObservation sameSwappedProduct realSealRoute realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have swappedTransportUnary : UnaryHistory swappedTransport :=
    unary_cont_closed windowBUnary windowAUnary swappedWindow
  have swappedProductUnary : UnaryHistory swappedProduct :=
    unary_cont_closed observationBUnary observationAUnary swappedObservation
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary realSealRoute
  have sourceAtRealSeal :
      hsame realSeal windowA ∨ hsame realSeal windowB ∨ hsame realSeal swappedProduct ∨
        hsame realSeal classifier ∨ hsame realSeal realSeal :=
    Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl realSeal))))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row swappedProduct ∨
              hsame row classifier ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row swappedProduct ∨
              hsame row classifier ∨ hsame row realSeal)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧
              (hsame row windowA ∨ hsame row windowB ∨ hsame row swappedProduct ∨
                hsame row classifier ∨ hsame row realSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtRealSeal
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
        | inl rowWindowA =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowWindowA)
        | inr tail =>
            cases tail with
            | inl rowWindowB =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowWindowB))
            | inr tail =>
                cases tail with
                | inl rowSwappedProduct =>
                    exact Or.inr
                      (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) rowSwappedProduct)))
                | inr tail =>
                    cases tail with
                    | inl rowClassifier =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl
                                (hsame_trans (hsame_symm sameRows) rowClassifier))))
                    | inr rowRealSeal =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) rowRealSeal))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact And.intro realSealPkg source
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, swappedTransportUnary, swappedProductUnary,
      classifierUnary, realSealUnary, sameSwappedProduct, swappedWindow, swappedObservation,
      classifierRoute, realSealRoute, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
