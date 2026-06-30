import BEDC.Derived.BolzanoWeierstrassSelectorUp.WindowObligation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSelectorRootWindow [AskSetup] [PackageSetup]
    {B M Q W D R E _H _C P N selectedWindow dyadicRead regularRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B M selectedWindow →
      Cont selectedWindow Q W →
        Cont W D dyadicRead →
          Cont dyadicRead R regularRead →
            Cont regularRead E realSeal →
              UnaryHistory B →
                UnaryHistory M →
                  UnaryHistory Q →
                    UnaryHistory D →
                      UnaryHistory R →
                        UnaryHistory E →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row W ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row B ∨ hsame row M ∨ hsame row Q ∨
                                      hsame row W ∨ hsame row D ∨ hsame row R ∨
                                        hsame row E)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                                  hsame ∧ UnaryHistory selectedWindow ∧ UnaryHistory W ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory regularRead ∧
                              UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro selectedRoute windowRoute dyadicRoute regularRoute sealRoute unaryB unaryM unaryQ
    unaryD unaryR unaryE provenancePkg localNamePkg
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed unaryB unaryM selectedRoute
  have windowUnary : UnaryHistory W :=
    unary_cont_closed selectedUnary unaryQ windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary unaryR regularRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularUnary unaryE sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row W ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row M ∨ hsame row Q ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row E)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro W ⟨hsame_refl W, windowUnary⟩
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, selectedUnary, windowUnary, dyadicUnary, regularUnary, sealUnary⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
