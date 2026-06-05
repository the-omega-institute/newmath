import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureSequenceWindowCoverage [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N requestRead windowRead handoffRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory S →
        UnaryHistory Q →
          UnaryHistory L →
            UnaryHistory U →
              UnaryHistory W →
                UnaryHistory R →
                  UnaryHistory A →
                    Cont T Q requestRead →
                      Cont requestRead U windowRead →
                        Cont windowRead W handoffRead →
                          Cont handoffRead R sealRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row T ∨ hsame row S ∨ hsame row Q ∨
                                        hsame row U ∨ hsame row W ∨ hsame row handoffRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont T Q requestRead ∧
                                        Cont requestRead U windowRead ∧
                                          Cont windowRead W handoffRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro tUnary _sUnary qUnary _lUnary uUnary wUnary rUnary _aUnary requestRoute
    windowRoute handoffRoute sealRoute pPkg nPkg
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed tUnary qUnary requestRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed requestUnary uUnary windowRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed windowUnary wUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary rUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row Q ∨ hsame row U ∨ hsame row W ∨
              hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T Q requestRead ∧ Cont requestRead U windowRead ∧
              Cont windowRead W handoffRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, requestRoute, windowRoute, handoffRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.SequentialClosureUp
