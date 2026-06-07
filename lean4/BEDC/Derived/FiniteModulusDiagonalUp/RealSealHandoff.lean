import BEDC.Derived.FiniteModulusDiagonalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteModulusDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteModulusDiagonalCarrier [AskSetup] [PackageSetup]
    (M S T Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory Q ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem FiniteModulusDiagonalRealSealHandoff [AskSetup] [PackageSetup]
    {M S T Q E H C P N windowRead toleranceRead readbackRead realSealRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteModulusDiagonalCarrier M S T Q E H C P N bundle pkg ->
      UnaryHistory M ->
        UnaryHistory S ->
          UnaryHistory T ->
            UnaryHistory Q ->
              UnaryHistory E ->
                UnaryHistory N ->
                  Cont M S windowRead ->
                    Cont windowRead T toleranceRead ->
                      Cont toleranceRead Q readbackRead ->
                        Cont readbackRead E realSealRead ->
                          Cont realSealRead N namedRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M ∨ hsame row S ∨ hsame row T ∨
                                        hsame row Q ∨ hsame row E ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont M S windowRead ∧
                                        Cont windowRead T toleranceRead ∧
                                          Cont toleranceRead Q readbackRead ∧
                                            Cont readbackRead E realSealRead ∧
                                              Cont realSealRead N namedRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                                    UnaryHistory readbackRead ∧ UnaryHistory realSealRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier unaryM unaryS unaryT unaryQ unaryE unaryN windowRoute toleranceRoute
    readbackRoute sealRoute namedRoute packageP packageN
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryM unaryS windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary unaryT toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryQ readbackRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed readbackUnary unaryE sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realSealUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row S ∨ hsame row T ∨ hsame row Q ∨ hsame row E ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M S windowRead ∧ Cont windowRead T toleranceRead ∧
              Cont toleranceRead Q readbackRead ∧ Cont readbackRead E realSealRead ∧
                Cont realSealRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, readbackRoute, sealRoute, namedRoute,
          packageP, packageN⟩
  }
  exact
    ⟨cert, windowUnary, toleranceUnary, readbackUnary, realSealUnary, namedUnary⟩

end BEDC.Derived.FiniteModulusDiagonalUp
