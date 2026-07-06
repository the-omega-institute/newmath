import BEDC.Derived.BaireOneFunctionUp.OscillationLocality

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireOneFunctionCarrier_lowersemicontinuous_public_nonescape_certificate
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N lscRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont R L lscRead ->
        PkgSig bundle lscRead pkg ->
          Cont L C publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row lscRead ∨ hsame row publicRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row lscRead ∨
                          hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R L lscRead ∧ Cont L C publicRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle lscRead pkg ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory lscRead ∧ UnaryHistory publicRead ∧
                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier lscRoute lscPkg publicRoute publicPkg
  have lscHandoff :=
    BaireOneFunctionCarrier_lowersemicontinuous_handoff
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (lscRead := lscRead) (bundle := bundle)
      (pkg := pkg) carrier lscRoute lscPkg
  obtain ⟨_lscCert, lscUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    provenancePkg⟩ := lscHandoff
  have publicBoundary :=
    BaireOneFunctionCarrier_public_export_locality_boundary
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (publicRead := publicRead) (bundle := bundle)
      (pkg := pkg) carrier publicRoute publicPkg
  obtain ⟨_publicCert, publicUnary⟩ := publicBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lscRead ∨ hsame row publicRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row lscRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R L lscRead ∧ Cont L C publicRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle lscRead pkg ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lscRead
        ⟨Or.inl (hsame_refl lscRead), lscUnary⟩
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
        constructor
        · cases source.left with
          | inl sameLsc =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameLsc)
          | inr samePublic =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) samePublic)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLsc =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl sameLsc
      | inr samePublic =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr samePublic
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lscRoute, publicRoute, provenancePkg, lscPkg, publicPkg⟩
  }
  exact ⟨cert, lscUnary, publicUnary, provenancePkg⟩

end BEDC.Derived.BaireOneFunctionUp
