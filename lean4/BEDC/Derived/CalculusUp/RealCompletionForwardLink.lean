import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRealCompletionForwardLink [AskSetup] [PackageSetup]
    {C L Q Y R N P limitRead dyadicRead realRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory L →
        UnaryHistory Q →
          UnaryHistory Y →
            UnaryHistory R →
              UnaryHistory N →
                Cont C L limitRead →
                  Cont limitRead Q dyadicRead →
                    Cont dyadicRead R realRead →
                      Cont realRead N endpointRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle endpointRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row L ∨ hsame row Q ∨ hsame row Y ∨
                                    hsame row R ∨ hsame row realRead ∨
                                      hsame row endpointRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont C L limitRead ∧
                                    Cont limitRead Q dyadicRead ∧
                                      Cont dyadicRead R realRead ∧
                                        Cont realRead N endpointRead ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle endpointRead pkg)
                                hsame ∧
                              UnaryHistory limitRead ∧ UnaryHistory dyadicRead ∧
                                UnaryHistory realRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro cUnary lUnary qUnary _yUnary rUnary nUnary limitRoute dyadicRoute realRoute
    endpointRoute provenancePkg endpointPkg
  have limitUnary : UnaryHistory limitRead := unary_cont_closed cUnary lUnary limitRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed limitUnary qUnary dyadicRoute
  have realUnary : UnaryHistory realRead := unary_cont_closed dyadicUnary rUnary realRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed realUnary nUnary endpointRoute
  have sourceEndpoint :
      (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row) endpointRead := by
    exact ⟨hsame_refl endpointRead, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row Q ∨ hsame row Y ∨ hsame row R ∨
              hsame row realRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C L limitRead ∧ Cont limitRead Q dyadicRead ∧
              Cont dyadicRead R realRead ∧ Cont realRead N endpointRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead sourceEndpoint
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, limitRoute, dyadicRoute, realRoute, endpointRoute, provenancePkg,
          endpointPkg⟩
  }
  exact ⟨cert, limitUnary, dyadicUnary, realUnary, endpointUnary⟩

end BEDC.Derived.CalculusUp
