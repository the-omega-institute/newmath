import BEDC.Derived.RegularCauchyWindowFusionUp.SharedWindowHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionRealSealNonescape [AskSetup] [PackageSetup]
    {R W S D E H C P N seedWindow regularDyadic realSeal sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory E →
              UnaryHistory H →
                Cont R W seedWindow →
                  Cont S D regularDyadic →
                    Cont seedWindow regularDyadic realSeal →
                      Cont realSeal H sealedRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle sealedRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row R ∨ hsame row W ∨ hsame row S ∨
                                    hsame row D ∨ hsame row E ∨ hsame row H ∨
                                      hsame row realSeal ∨ hsame row sealedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont R W seedWindow ∧
                                    Cont S D regularDyadic ∧
                                      Cont seedWindow regularDyadic realSeal ∧
                                        Cont realSeal H sealedRead ∧
                                          PkgSig bundle sealedRead pkg)
                                hsame ∧
                              UnaryHistory seedWindow ∧ UnaryHistory regularDyadic ∧
                                UnaryHistory realSeal ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro rUnary wUnary sUnary dUnary _eUnary hUnary seedRoute dyadicRoute
    realSealRoute sealSupport provenancePkg sealedPkg
  have handoff :
      UnaryHistory seedWindow ∧ UnaryHistory regularDyadic ∧ UnaryHistory realSeal ∧
        Cont R W seedWindow ∧ Cont S D regularDyadic ∧
          Cont seedWindow regularDyadic realSeal ∧ PkgSig bundle P pkg :=
    RegularCauchyWindowFusionSharedWindowHandoff
      (_E := E) (_H := H) (_C := C) (_N := N)
      rUnary wUnary sUnary dUnary seedRoute dyadicRoute realSealRoute provenancePkg
  have seedUnary : UnaryHistory seedWindow := handoff.left
  have regularDyadicUnary : UnaryHistory regularDyadic := handoff.right.left
  have realSealUnary : UnaryHistory realSeal := handoff.right.right.left
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed realSealUnary hUnary sealSupport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row realSeal ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W seedWindow ∧ Cont S D regularDyadic ∧
              Cont seedWindow regularDyadic realSeal ∧ Cont realSeal H sealedRead ∧
                PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead
        ⟨hsame_refl sealedRead, sealedUnary⟩
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
        ⟨source.right, seedRoute, dyadicRoute, realSealRoute, sealSupport, sealedPkg⟩
  }
  exact ⟨cert, seedUnary, regularDyadicUnary, realSealUnary, sealedUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
