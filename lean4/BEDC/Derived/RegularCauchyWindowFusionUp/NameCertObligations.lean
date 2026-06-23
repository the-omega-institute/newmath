import BEDC.Derived.RegularCauchyWindowFusionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionNameCertObligations [AskSetup] [PackageSetup]
    {R W S D E _H _C P _N seedWindow realSeal named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory E →
              Cont R W seedWindow →
                Cont S D realSeal →
                  Cont seedWindow realSeal named →
                    PkgSig bundle P pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row named ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨
                              hsame row E ∨ hsame row seedWindow ∨ hsame row realSeal ∨
                                hsame row named)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont R W seedWindow ∧
                              Cont S D realSeal ∧ Cont seedWindow realSeal named ∧
                                PkgSig bundle P pkg)
                          hsame ∧
                        UnaryHistory seedWindow ∧ UnaryHistory realSeal ∧
                          UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rUnary wUnary sUnary dUnary _eUnary seedRoute realSealRoute namedRoute packageRead
  have seedUnary : UnaryHistory seedWindow :=
    unary_cont_closed rUnary wUnary seedRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed sUnary dUnary realSealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed seedUnary realSealUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨
              hsame row E ∨ hsame row seedWindow ∨ hsame row realSeal ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W seedWindow ∧ Cont S D realSeal ∧
              Cont seedWindow realSeal named ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
              (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, seedRoute, realSealRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, seedUnary, realSealUnary, namedUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
