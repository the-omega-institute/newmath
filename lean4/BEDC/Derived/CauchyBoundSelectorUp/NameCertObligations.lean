import BEDC.Derived.CauchyBoundSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyBoundSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyBoundSelectorNamecertObligations [AskSetup] [PackageSetup]
    {source bound selector transport replay provenance localName selectorRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory bound →
        UnaryHistory selector →
          UnaryHistory transport →
            UnaryHistory replay →
              Cont source bound selectorRead →
                Cont selectorRead replay publicRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle localName pkg →
                      PkgSig bundle publicRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row bound ∨ hsame row selector ∨
                                hsame row selectorRead ∨ hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle localName pkg ∧ PkgSig bundle publicRead pkg)
                            hsame ∧
                          UnaryHistory selectorRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CauchyBoundSelectorUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sourceUnary boundUnary _selectorUnary _transportUnary replayUnary selectorRoute publicRoute
    provenancePkg localNamePkg publicPkg
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed sourceUnary boundUnary selectorRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed selectorReadUnary replayUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row bound ∨ hsame row selector ∨
              hsame row selectorRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, publicPkg⟩
  }
  exact ⟨cert, selectorReadUnary, publicReadUnary⟩

end BEDC.Derived.CauchyBoundSelectorUp
