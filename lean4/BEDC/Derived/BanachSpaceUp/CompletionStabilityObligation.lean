import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceCompletionStabilityObligation [AskSetup] [PackageSetup]
    {M Q S R E P requestRead handoffRead realRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory Q ->
        UnaryHistory S ->
          UnaryHistory R ->
            UnaryHistory E ->
              PkgSig bundle P pkg ->
                Cont M Q requestRead ->
                  Cont requestRead S handoffRead ->
                    Cont handoffRead R realRead ->
                      Cont realRead E stableRead ->
                        SemanticNameCert
                            (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
                                hsame row requestRead ∨ hsame row handoffRead ∨
                                  hsame row realRead ∨ hsame row stableRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont M Q requestRead ∧
                                Cont requestRead S handoffRead ∧
                                  Cont handoffRead R realRead ∧ Cont realRead E stableRead ∧
                                    PkgSig bundle P pkg)
                            hsame ∧
                          UnaryHistory requestRead ∧ UnaryHistory handoffRead ∧
                            UnaryHistory realRead ∧ UnaryHistory stableRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro mUnary qUnary sUnary rUnary eUnary provenancePkg requestRoute handoffRoute
    realRoute stableRoute
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed mUnary qUnary requestRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed requestUnary sUnary handoffRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed handoffUnary rUnary realRoute
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed realUnary eUnary stableRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
              hsame row requestRead ∨ hsame row handoffRead ∨ hsame row realRead ∨
                hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q requestRead ∧ Cont requestRead S handoffRead ∧
              Cont handoffRead R realRead ∧ Cont realRead E stableRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro stableRead ⟨hsame_refl stableRead, stableUnary⟩
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
      exact
        ⟨source.right, requestRoute, handoffRoute, realRoute, stableRoute,
          provenancePkg⟩
  }
  exact ⟨cert, requestUnary, handoffUnary, realUnary, stableUnary⟩

end BEDC.Derived.BanachSpaceUp
