import BEDC.Derived.TaoMetastableCauchyUp.TasteGate

namespace BEDC.Derived.TaoMetastableCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TaoMetastableCauchyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {q F W D S R E B H C P N windowRead readbackRead sealRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory q ∧ UnaryHistory F ∧ UnaryHistory W ∧ UnaryHistory D ∧
      UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory B ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          PkgSig bundle P pkg) →
      Cont q F windowRead →
        Cont windowRead D readbackRead →
          Cont readbackRead E sealRead →
            Cont sealRead B boundaryRead →
              PkgSig bundle boundaryRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row q ∨ hsame row F ∨ hsame row W ∨ hsame row D ∨
                        hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row B ∨
                          hsame row boundaryRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle boundaryRead pkg)
                    hsame ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rows windowRoute readbackRoute sealRoute boundaryRoute boundaryPkg
  obtain ⟨qUnary, fUnary, _wUnary, dUnary, _sUnary, _rUnary, eUnary, bUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, pPkg⟩ := rows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed qUnary fUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary dUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnary bUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row F ∨ hsame row W ∨ hsame row D ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row B ∨
                hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, pPkg, boundaryPkg⟩
    }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.TaoMetastableCauchyUp
