import BEDC.Derived.BetaSubstitutionPreservationUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BetaSubstitutionPreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BetaSubstitutionPreservationNonescape [AskSetup] [PackageSetup]
    {body argument redex codomain substitutedBody substitutedCodomain ledger transport routes
      provenance name boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory body →
      UnaryHistory argument →
        UnaryHistory redex →
          UnaryHistory codomain →
            UnaryHistory substitutedBody →
              UnaryHistory substitutedCodomain →
                UnaryHistory ledger →
                  UnaryHistory transport →
                    UnaryHistory routes →
                      UnaryHistory provenance →
                        UnaryHistory name →
                          Cont redex codomain substitutedBody →
                            Cont substitutedBody substitutedCodomain boundary →
                              PkgSig bundle boundary pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row body ∨ hsame row argument ∨
                                        hsame row redex ∨ hsame row codomain ∨
                                          hsame row substitutedBody ∨
                                            hsame row substitutedCodomain ∨ hsame row ledger ∨
                                              hsame row boundary)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle boundary pkg ∧
                                        Cont substitutedBody substitutedCodomain boundary)
                                    hsame ∧
                                  UnaryHistory boundary := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _bodyUnary _argumentUnary redexUnary codomainUnary substitutedBodyUnary
    substitutedCodomainUnary _ledgerUnary _transportUnary _routesUnary _provenanceUnary
    _nameUnary redexClosure boundaryClosure boundaryPkg
  have substitutedBodyUnaryFromRoute : UnaryHistory substitutedBody :=
    unary_cont_closed redexUnary codomainUnary redexClosure
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed substitutedBodyUnary substitutedCodomainUnary boundaryClosure
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row body ∨ hsame row argument ∨ hsame row redex ∨ hsame row codomain ∨
              hsame row substitutedBody ∨ hsame row substitutedCodomain ∨ hsame row ledger ∨
                hsame row boundary)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle boundary pkg ∧
              Cont substitutedBody substitutedCodomain boundary)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundary ⟨hsame_refl boundary, boundaryUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryPkg, boundaryClosure⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.BetaSubstitutionPreservationUp
