import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived

def LocatedDyadicCompletionUp : Prop := True

namespace LocatedDyadicCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedDyadicCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D S R L E H C P N windowRead regularRead locatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D -> UnaryHistory S -> UnaryHistory R -> UnaryHistory L ->
      UnaryHistory E -> UnaryHistory H -> UnaryHistory C ->
        Cont D S windowRead -> Cont windowRead R regularRead ->
          Cont regularRead L locatedRead -> Cont locatedRead E sealRead ->
            PkgSig bundle P pkg -> PkgSig bundle N pkg -> PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row L ∨
                      hsame row E ∨ hsame row windowRead ∨ hsame row regularRead ∨
                        hsame row locatedRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D S windowRead ∧
                      Cont windowRead R regularRead ∧ Cont regularRead L locatedRead ∧
                        Cont locatedRead E sealRead ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory locatedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame Cont SemanticNameCert
  intro unaryD unaryS unaryR unaryL unaryE _unaryH _unaryC
  intro windowCont regularCont locatedCont sealCont _provenancePkg _namePkg sealPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryD unaryS windowCont
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary unaryR regularCont
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed regularUnary unaryL locatedCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed locatedUnary unaryE sealCont
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead :=
    ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row L ∨
              hsame row E ∨ hsame row windowRead ∨ hsame row regularRead ∨
                hsame row locatedRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S windowRead ∧ Cont windowRead R regularRead ∧
              Cont regularRead L locatedRead ∧ Cont locatedRead E sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro row source
      exact
        ⟨source.right, windowCont, regularCont, locatedCont, sealCont, sealPkg⟩
  }
  exact ⟨cert, windowUnary, regularUnary, locatedUnary, sealUnary⟩

end LocatedDyadicCompletionUp

end BEDC.Derived
