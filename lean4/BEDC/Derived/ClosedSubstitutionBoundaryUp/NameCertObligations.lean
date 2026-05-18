import BEDC.Derived.ClosedSubstitutionBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedSubstitutionBoundary_namecert_obligations
    [AskSetup] [PackageSetup]
    {T D V K R Q H C P N nameRead obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory D →
        UnaryHistory V →
          UnaryHistory K →
            UnaryHistory R →
              UnaryHistory Q →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont K Q nameRead →
                      Cont nameRead C obligationRead →
                        hsame H BHist.Empty →
                          PkgSig bundle P pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row N ∧ Cont K Q nameRead ∧
                                    Cont nameRead C obligationRead ∧ hsame H BHist.Empty)
                                (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory nameRead ∧ UnaryHistory obligationRead ∧
                                Cont K Q nameRead ∧ Cont nameRead C obligationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro _unaryT _unaryD _unaryV unaryK _unaryR unaryQ unaryC unaryN
    nameRoute obligationRoute emptyTransport pkgSig
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed unaryK unaryQ nameRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed nameUnary unaryC obligationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row N ∧ Cont K Q nameRead ∧ Cont nameRead C obligationRead ∧
              hsame H BHist.Empty)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro N ⟨hsame_refl N, unaryN⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    · intro _row source
      exact ⟨source.left, nameRoute, obligationRoute, emptyTransport⟩
    · intro _row source
      exact ⟨source.left, pkgSig⟩
  exact ⟨cert, nameUnary, obligationUnary, nameRoute, obligationRoute⟩

end BEDC.Derived.ClosedSubstitutionBoundaryUp
