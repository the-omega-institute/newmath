import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierSealBoundary [AskSetup] [PackageSetup]
    {leftName rightName window leftTol rightTol classifier _leftRead _rightRead _transport
      _replay provenance sealRow localName classifierRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftName →
      UnaryHistory rightName →
        UnaryHistory window →
          UnaryHistory leftTol →
            UnaryHistory rightTol →
              UnaryHistory classifier →
                UnaryHistory sealRow →
                  Cont window leftTol classifierRead →
                    Cont classifierRead rightTol sealRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row leftName ∨ hsame row rightName ∨
                                  hsame row window ∨ hsame row leftTol ∨
                                    hsame row rightTol ∨ hsame row classifier ∨
                                      hsame row sealRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont window leftTol classifierRead ∧
                                  Cont classifierRead rightTol sealRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory classifierRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert PkgSig
  intro _leftUnary _rightUnary windowUnary leftTolUnary rightTolUnary _classifierUnary
    _sealUnary classifierRoute sealRoute provenancePkg localNamePkg
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary leftTolUnary classifierRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierReadUnary rightTolUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row leftName ∨ hsame row rightName ∨ hsame row window ∨
              hsame row leftTol ∨ hsame row rightTol ∨ hsame row classifier ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window leftTol classifierRead ∧
              Cont classifierRead rightTol sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact ⟨source.right, classifierRoute, sealRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, classifierReadUnary, sealReadUnary⟩

end BEDC.Derived.RealNameClassifierUp
