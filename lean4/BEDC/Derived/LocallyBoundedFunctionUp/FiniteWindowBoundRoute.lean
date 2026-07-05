import BEDC.Derived.LocallyBoundedFunctionUp.TasteGate

namespace BEDC.Derived.LocallyBoundedFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyBoundedFunctionCarrier_finite_window_policy_transport [AskSetup] [PackageSetup]
    {K F V B W R D A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocallyBoundedFunctionCarrier K F V B W R D A H C P N bundle pkg →
      (UnaryHistory N ∧ Cont K F V ∧ PkgSig bundle P pkg) ∧
        (UnaryHistory N ∧ Cont W R D ∧ Cont D A C ∧ PkgSig bundle P pkg) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  have obligations :=
    LocallyBoundedFunctionCarrier_namecert_obligations
      (K := K) (F := F) (V := V) (B := B) (W := W) (R := R) (D := D)
      (A := A) (H := H) (C := C) (P := P) (N := N) (bundle := bundle)
      (pkg := pkg) carrier
  exact
    semanticNameCert_pattern_ledger_transport obligations.left
      (hsame_refl N) carrier

theorem LocallyBoundedFunctionFiniteWindowBoundRoute [AskSetup] [PackageSetup]
    {K F V B W R D A H C P N windowRead boundRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory R →
        UnaryHistory B →
          UnaryHistory D →
            Cont W R windowRead →
              Cont windowRead B boundRead →
                Cont boundRead D sealRead →
                  PkgSig bundle sealRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K ∨ hsame row F ∨ hsame row V ∨ hsame row B ∨
                            hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont W R windowRead ∧
                            Cont windowRead B boundRead ∧ Cont boundRead D sealRead ∧
                              PkgSig bundle sealRead pkg)
                        hsame ∧
                      UnaryHistory windowRead ∧ UnaryHistory boundRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro wUnary rUnary bUnary dUnary windowRoute boundRoute sealRoute sealPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed windowUnary bUnary boundRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed boundUnary dUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row V ∨ hsame row B ∨
              hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead B boundRead ∧
              Cont boundRead D sealRead ∧ PkgSig bundle sealRead pkg)
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, boundRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, windowUnary, boundUnary, sealUnary⟩

end BEDC.Derived.LocallyBoundedFunctionUp
