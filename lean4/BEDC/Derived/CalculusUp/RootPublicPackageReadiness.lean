import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootPublicPackageReadiness [AskSetup] [PackageSetup]
    {R L C D I Q _H _T P N derivativeRead integralRead limitRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory L →
        UnaryHistory C →
          UnaryHistory D →
            UnaryHistory I →
              UnaryHistory Q →
                UnaryHistory N →
                  Cont C D derivativeRead →
                    Cont C I integralRead →
                      Cont C L limitRead →
                        Cont Q R realRead →
                          Cont realRead N publicRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row C ∨ hsame row D ∨ hsame row I ∨
                                        hsame row L ∨ hsame row R ∨ hsame row Q ∨
                                          hsame row realRead ∨ hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont C D derivativeRead ∧
                                        Cont C I integralRead ∧ Cont C L limitRead ∧
                                          Cont Q R realRead ∧ Cont realRead N publicRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory derivativeRead ∧
                                    UnaryHistory integralRead ∧ UnaryHistory limitRead ∧
                                      UnaryHistory realRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryR unaryL unaryC unaryD unaryI unaryQ unaryN derivativeRoute integralRoute
    limitRoute realRoute publicRoute provenancePkg namePkg
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed unaryC unaryD derivativeRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed unaryC unaryI integralRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed unaryC unaryL limitRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryQ unaryR realRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary unaryN publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨ hsame row R ∨
              hsame row Q ∨ hsame row realRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeRead ∧ Cont C I integralRead ∧
              Cont C L limitRead ∧ Cont Q R realRead ∧ Cont realRead N publicRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        ⟨source.right, derivativeRoute, integralRoute, limitRoute, realRoute, publicRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, derivativeUnary, integralUnary, limitUnary, realUnary, publicUnary⟩

end BEDC.Derived.CalculusUp
