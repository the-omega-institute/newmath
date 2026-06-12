import BEDC.Derived.CauchyLocatedApartnessUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyLocatedApartnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLocatedApartnessLocatorApartnessHandoff [AskSetup] [PackageSetup]
    {locator leftGap rightGap stream readback dyadic sealRow transport replay provenance localName
      locatorRead regularRead toleranceRead apartnessRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory locator → UnaryHistory stream → UnaryHistory readback → UnaryHistory dyadic →
      UnaryHistory leftGap → UnaryHistory rightGap → UnaryHistory sealRow → UnaryHistory transport →
        UnaryHistory replay → Cont locator stream locatorRead →
          Cont locatorRead readback regularRead →
            Cont regularRead dyadic toleranceRead →
              Cont toleranceRead leftGap apartnessRead →
                Cont apartnessRead sealRow finalRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle localName pkg →
                      SemanticNameCert
                        (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row locator ∨ hsame row stream ∨ hsame row readback ∨
                            hsame row dyadic ∨ hsame row leftGap ∨ hsame row rightGap ∨
                              hsame row sealRow ∨ hsame row finalRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont regularRead dyadic toleranceRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                        hsame ∧ UnaryHistory locatorRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory toleranceRead ∧ UnaryHistory apartnessRead ∧
                            UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro locatorUnary streamUnary readbackUnary dyadicUnary leftGapUnary _rightGapUnary sealUnary
    _transportUnary _replayUnary locatorRoute regularRoute toleranceRoute apartnessRoute finalRoute
    provenancePkg localNamePkg
  have locatorReadUnary : UnaryHistory locatorRead :=
    unary_cont_closed locatorUnary streamUnary locatorRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed locatorReadUnary readbackUnary regularRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed regularReadUnary dyadicUnary toleranceRoute
  have apartnessReadUnary : UnaryHistory apartnessRead :=
    unary_cont_closed toleranceReadUnary leftGapUnary apartnessRoute
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed apartnessReadUnary sealUnary finalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row locator ∨ hsame row stream ∨ hsame row readback ∨
              hsame row dyadic ∨ hsame row leftGap ∨ hsame row rightGap ∨
                hsame row sealRow ∨ hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regularRead dyadic toleranceRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finalRead ⟨hsame_refl finalRead, finalUnary⟩
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
      exact ⟨source.right, toleranceRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, locatorReadUnary, regularReadUnary, toleranceReadUnary, apartnessReadUnary, finalUnary⟩

end BEDC.Derived.CauchyLocatedApartnessUp
